/*
 * subnet-tools.js — shared calculator logic for 5pings Subnet Calculator.
 * Loaded via a plain <script src="../assets/subnet-tools.js"></script> tag
 * (not an ES module, so pages work when opened straight off disk too).
 * Every page's own inline <script> only wires up the DOM elements it has
 * and calls into window.SubnetTools for the actual math/rendering.
 */
(function (global) {
  "use strict";

  const MAX_SPLIT_ROWS = 4096;
  const MAX_VISUAL_ROWS = 256;

  // ---------------------------------------------------------------- IPv4 math
  function ipToInt(str) {
    const parts = String(str).trim().split(".");
    if (parts.length !== 4) return null;
    let result = 0;
    for (const p of parts) {
      if (!/^\d{1,3}$/.test(p)) return null;
      if (p.length > 1 && p[0] === "0") return null; // no leading zeros
      const n = parseInt(p, 10);
      if (n < 0 || n > 255) return null;
      result = (result * 256) + n;
    }
    return result >>> 0;
  }

  function intToIp(n) {
    n = n >>> 0;
    return [(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255].join(".");
  }

  function prefixToMaskInt(prefix) {
    if (prefix <= 0) return 0;
    if (prefix >= 32) return 0xFFFFFFFF >>> 0;
    return (0xFFFFFFFF << (32 - prefix)) >>> 0;
  }

  function maskToPrefix(maskStr) {
    const maskInt = ipToInt(maskStr);
    if (maskInt === null) return null;
    let prefix = 0;
    for (let i = 31; i >= 0; i--) {
      if ((maskInt >>> i) & 1) prefix++;
      else break;
    }
    if (prefixToMaskInt(prefix) !== maskInt) return null; // not a contiguous mask
    return prefix;
  }

  function toBinaryOctets(ipInt) {
    return [24, 16, 8, 0]
      .map((shift) => (((ipInt >>> shift) & 255).toString(2).padStart(8, "0")))
      .join(".");
  }

  function ipClass(ipInt) {
    const first = (ipInt >>> 24) & 255;
    if (first < 128) return "A";
    if (first < 192) return "B";
    if (first < 224) return "C";
    if (first < 240) return "D (Multicast)";
    return "E (Reserved)";
  }

  // Mirrors Python's ipaddress.IPv4Address.is_private ranges.
  const PRIVATE_RANGES = [
    ["0.0.0.0", 8], ["10.0.0.0", 8], ["127.0.0.0", 8], ["169.254.0.0", 16],
    ["172.16.0.0", 12], ["192.0.0.0", 29], ["192.0.0.170", 31], ["192.0.2.0", 24],
    ["192.168.0.0", 16], ["198.18.0.0", 15], ["198.51.100.0", 24],
    ["203.0.113.0", 24], ["240.0.0.0", 4], ["255.255.255.255", 32],
  ].map(([base, prefix]) => ({ base: ipToInt(base), mask: prefixToMaskInt(prefix) }));

  function isPrivateIp(ipInt) {
    return PRIVATE_RANGES.some(({ base, mask }) => ((ipInt & mask) >>> 0) === ((base & mask) >>> 0));
  }

  function bitLength(n) {
    let bits = 0;
    while (n > 0) { bits++; n = Math.floor(n / 2); }
    return bits;
  }

  // ---------------------------------------------------------------- IPv6 math
  function expandIPv6(str) {
    str = String(str).trim();
    if (!str) return null;
    str = str.split("%")[0]; // strip zone index
    if (!/^[0-9A-Fa-f:]+$/.test(str)) return null;
    if ((str.match(/::/g) || []).length > 1) return null;

    let head, tail;
    const hasDouble = str.includes("::");
    if (hasDouble) {
      const parts = str.split("::");
      head = parts[0]; tail = parts[1];
    } else {
      head = str; tail = "";
    }
    const headParts = head === "" ? [] : head.split(":");
    const tailParts = tail === "" ? [] : tail.split(":");

    if (!hasDouble && headParts.length !== 8) return null;
    const missing = 8 - headParts.length - tailParts.length;
    if (hasDouble ? missing < 0 : missing !== 0) return null;

    const allParts = headParts.concat(Array(Math.max(missing, 0)).fill("0"), tailParts);
    if (allParts.length !== 8) return null;

    const result = [];
    for (const p of allParts) {
      if (!/^[0-9A-Fa-f]{1,4}$/.test(p)) return null;
      result.push(p.padStart(4, "0").toLowerCase());
    }
    return result;
  }

  function ipv6ToBigInt(str) {
    const hextets = expandIPv6(str);
    if (!hextets) return null;
    let result = 0n;
    for (const h of hextets) result = (result << 16n) | BigInt(parseInt(h, 16));
    return result;
  }

  function bigIntToHextets(big) {
    big = BigInt.asUintN(128, big);
    const out = [];
    for (let i = 7; i >= 0; i--) {
      const part = (big >> BigInt(i * 16)) & 0xFFFFn;
      out.push(part.toString(16).padStart(4, "0"));
    }
    return out;
  }

  function compressIPv6(hextetsPadded) {
    const stripped = hextetsPadded.map((h) => h.replace(/^0+(?=.)/, ""));
    let bestStart = -1, bestLen = 0, curStart = -1, curLen = 0;
    for (let i = 0; i < 8; i++) {
      if (stripped[i] === "0") {
        if (curStart === -1) curStart = i;
        curLen++;
      } else {
        if (curLen > bestLen) { bestLen = curLen; bestStart = curStart; }
        curStart = -1; curLen = 0;
      }
    }
    if (curLen > bestLen) { bestLen = curLen; bestStart = curStart; }
    if (bestLen < 2) return stripped.join(":");
    const before = stripped.slice(0, bestStart).join(":");
    const after = stripped.slice(bestStart + bestLen).join(":");
    return `${before}::${after}`;
  }

  function v6PrefixMask(prefix) {
    const full = (1n << 128n) - 1n;
    if (prefix <= 0) return 0n;
    if (prefix >= 128) return full;
    const hostBits = BigInt(128 - prefix);
    return (full >> hostBits) << hostBits;
  }

  function parseV6Cidr(cidr) {
    const idx = cidr.lastIndexOf("/");
    const ipStr = idx === -1 ? cidr : cidr.slice(0, idx);
    const prefix = idx === -1 ? 128 : parseInt(cidr.slice(idx + 1), 10);
    return { base: ipv6ToBigInt(ipStr), mask: v6PrefixMask(prefix) };
  }

  const IPV6_TYPE_RANGES = [
    ["::1/128", "Loopback"],
    ["::/128", "Unspecified"],
    ["::ffff:0:0/96", "IPv4-mapped"],
    ["fc00::/7", "Unique Local (ULA)"],
    ["fe80::/10", "Link-Local"],
    ["ff00::/8", "Multicast"],
    ["2001:db8::/32", "Documentation"],
    ["2000::/3", "Global Unicast"],
  ].map(([cidr, label]) => Object.assign({ label }, parseV6Cidr(cidr)));

  function ipv6Type(ipBig) {
    for (const r of IPV6_TYPE_RANGES) {
      if ((ipBig & r.mask) === (r.base & r.mask)) return r.label;
    }
    return "Global Unicast / Other";
  }

  // -------------------------------------------------------------- utilities
  function showError(el, message) {
    el.textContent = message;
    el.classList.toggle("show", Boolean(message));
  }

  function showToast(msg) {
    let toast = document.getElementById("appToast");
    if (!toast) {
      toast = document.createElement("div");
      toast.id = "appToast";
      toast.className = "toast";
      document.body.appendChild(toast);
    }
    toast.textContent = msg;
    toast.classList.add("show");
    clearTimeout(toast._t);
    toast._t = setTimeout(() => toast.classList.remove("show"), 1300);
  }

  function copyText(text) {
    const fallback = () => {
      const ta = document.createElement("textarea");
      ta.value = text;
      ta.style.position = "fixed";
      ta.style.left = "-9999px";
      document.body.appendChild(ta);
      ta.select();
      try { document.execCommand("copy"); } catch (e) { /* ignore */ }
      document.body.removeChild(ta);
    };
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(
        () => showToast("Copied!"),
        () => { fallback(); showToast("Copied!"); }
      );
    } else {
      fallback();
      showToast("Copied!");
    }
  }

  function renderRowsWithCopy(tbody, rows) {
    tbody.innerHTML = "";
    for (const [field, value] of rows) {
      const tr = document.createElement("tr");
      const th = document.createElement("td");
      th.textContent = field;
      const td = document.createElement("td");
      td.textContent = value;
      const tdCopy = document.createElement("td");
      const btn = document.createElement("button");
      btn.type = "button";
      btn.className = "copy-btn";
      btn.title = "Copy value";
      btn.textContent = "⧉";
      btn.addEventListener("click", () => copyText(String(value)));
      tdCopy.appendChild(btn);
      tr.appendChild(th);
      tr.appendChild(td);
      tr.appendChild(tdCopy);
      tbody.appendChild(tr);
    }
  }

  function fillRefTable(tbody, rows) {
    for (const cols of rows) {
      const tr = document.createElement("tr");
      cols.forEach((v) => {
        const td = document.createElement("td");
        td.textContent = v;
        tr.appendChild(td);
      });
      tbody.appendChild(tr);
    }
  }

  // ------------------------------------------------------------ IPv4 compute
  function parseNetworkString(raw) {
    raw = String(raw || "").trim();
    if (!raw) return { error: "Provide an ip parameter, e.g. ?format=json&ip=192.168.1.0/24" };
    if (raw.includes("/")) {
      const [ipStr, cidrStr] = raw.split("/");
      const ipInt = ipToInt(ipStr);
      if (ipInt === null) return { error: `'${ipStr}' is not a valid IPv4 address.` };
      if (!/^\d{1,2}$/.test(cidrStr.trim())) return { error: `'${cidrStr}' is not a valid CIDR prefix.` };
      const prefix = parseInt(cidrStr.trim(), 10);
      if (prefix < 0 || prefix > 32) return { error: "CIDR prefix must be between 0 and 32." };
      return { ip: ipInt, prefix };
    }
    const ipInt = ipToInt(raw);
    if (ipInt === null) return { error: `'${raw}' is not a valid IPv4 address.` };
    return { ip: ipInt, prefix: 24 };
  }

  function computeFields(ip, prefix) {
    const maskInt = prefixToMaskInt(prefix);
    const networkInt = (ip & maskInt) >>> 0;
    const wildcardInt = (~maskInt) >>> 0;
    const broadcastInt = (networkInt | wildcardInt) >>> 0;
    const numAddresses = Math.pow(2, 32 - prefix);

    let firstHost, lastHost, usable;
    if (prefix <= 30) {
      firstHost = (networkInt + 1) >>> 0;
      lastHost = (broadcastInt - 1) >>> 0;
      usable = numAddresses - 2;
    } else if (prefix === 31) {
      firstHost = networkInt;
      lastHost = broadcastInt;
      usable = 2;
    } else {
      firstHost = lastHost = networkInt;
      usable = 1;
    }

    return {
      networkInt, maskInt, prefix,
      rows: [
        ["Entered IP Address", intToIp(ip)],
        ["Network Address", intToIp(networkInt)],
        ["Usable Host IP Range", `${intToIp(firstHost)} - ${intToIp(lastHost)}`],
        ["Broadcast Address", intToIp(broadcastInt)],
        ["Subnet Mask", intToIp(maskInt)],
        ["Wildcard Mask", intToIp(wildcardInt)],
        ["CIDR Notation", `/${prefix}`],
        ["Total Addresses", numAddresses.toLocaleString()],
        ["Usable Hosts", usable.toLocaleString()],
        ["IP Class", ipClass(ip)],
        ["IP Type", isPrivateIp(ip) ? "Private" : "Public"],
        ["Binary Subnet Mask", toBinaryOctets(maskInt)],
        ["Binary Network Address", toBinaryOctets(networkInt)],
        ["Binary IP Address", toBinaryOctets(ip)],
      ],
    };
  }

  function computeV6Fields(ipBig, prefix) {
    const maskBig = v6PrefixMask(prefix);
    const fullBig = (1n << 128n) - 1n;
    const networkBig = ipBig & maskBig;
    const wildcardBig = fullBig ^ maskBig;
    const lastBig = networkBig | wildcardBig;
    const totalAddresses = prefix >= 128 ? 1n : (1n << BigInt(128 - prefix));
    const hextetsFull = bigIntToHextets(ipBig);
    const hextetsNet = bigIntToHextets(networkBig);
    const hextetsLast = bigIntToHextets(lastBig);
    return {
      networkBig, maskBig, prefix,
      rows: [
        ["Compressed Address", compressIPv6(hextetsFull)],
        ["Expanded Address", hextetsFull.join(":")],
        ["Prefix Length", `/${prefix}`],
        ["Network Address", compressIPv6(hextetsNet)],
        ["Network Range", `${compressIPv6(hextetsNet)} - ${compressIPv6(hextetsLast)}`],
        ["Total Addresses", totalAddresses.toLocaleString()],
        ["Address Type", ipv6Type(ipBig)],
      ],
    };
  }

  // ----------------------------------------------------------- VLSM Planner
  function parseVlsmInput(text) {
    const lines = text.split("\n");
    const reqs = [];
    let idx = 1;
    for (const raw of lines) {
      const line = raw.trim();
      if (!line || line.startsWith("#")) continue;
      let name, hostsStr;
      if (line.includes(",")) {
        const parts = line.split(",");
        name = parts[0].trim() || `Subnet ${idx}`;
        hostsStr = parts.slice(1).join(",").trim();
      } else {
        name = `Subnet ${idx}`;
        hostsStr = line;
      }
      const hosts = parseInt(hostsStr, 10);
      if (!/^\d+$/.test(hostsStr) || Number.isNaN(hosts) || hosts < 1) {
        return { error: `Invalid host count on line: "${line}"` };
      }
      reqs.push({ name, hosts });
      idx++;
    }
    if (!reqs.length) return { error: "Enter at least one subnet requirement." };
    return { reqs };
  }

  function vlsmPlan(baseNetworkInt, basePrefix, requirements) {
    const withSize = requirements.map((r) => {
      const addrsNeeded = r.hosts + 2;
      let prefix = 32;
      for (let p = 32; p >= 0; p--) {
        if (Math.pow(2, 32 - p) >= addrsNeeded) { prefix = p; break; }
      }
      return Object.assign({}, r, { prefix, blockSize: Math.pow(2, 32 - prefix) });
    });
    withSize.sort((a, b) => b.blockSize - a.blockSize);

    const poolSize = Math.pow(2, 32 - basePrefix);
    let pointer = 0;
    const results = [];
    for (const r of withSize) {
      const rem = pointer % r.blockSize;
      if (rem !== 0) pointer += (r.blockSize - rem);
      if (pointer + r.blockSize > poolSize) {
        return { error: `Not enough space for "${r.name}" (needs /${r.prefix}, ${r.blockSize.toLocaleString()} addresses). Pool exhausted.` };
      }
      results.push(Object.assign({}, r, { networkInt: (baseNetworkInt + pointer) >>> 0 }));
      pointer += r.blockSize;
    }
    results.sort((a, b) => (a.networkInt >>> 0) - (b.networkInt >>> 0));
    return { results, usedAddresses: pointer, poolSize };
  }

  // ------------------------------------------------------- Reference tables
  const PRIVATE_RANGES_INFO_V4 = [
    ["0.0.0.0/8", "This Network", "RFC 791 — reserved source address block"],
    ["10.0.0.0/8", "Private (RFC 1918)", "Large private network block"],
    ["100.64.0.0/10", "Shared Address Space / CGNAT", "RFC 6598 — carrier-grade NAT"],
    ["127.0.0.0/8", "Loopback", "Localhost addresses"],
    ["169.254.0.0/16", "Link-Local (APIPA)", "Auto-assigned when no DHCP is available"],
    ["172.16.0.0/12", "Private (RFC 1918)", "Mid-size private network block"],
    ["192.0.0.0/24", "IETF Protocol Assignments", "Reserved for IETF protocols"],
    ["192.0.2.0/24", "Documentation (TEST-NET-1)", "Reserved for examples/docs"],
    ["192.168.0.0/16", "Private (RFC 1918)", "Small private network block"],
    ["198.18.0.0/15", "Benchmark Testing", "RFC 2544 network device testing"],
    ["198.51.100.0/24", "Documentation (TEST-NET-2)", "Reserved for examples/docs"],
    ["203.0.113.0/24", "Documentation (TEST-NET-3)", "Reserved for examples/docs"],
    ["224.0.0.0/4", "Multicast", "Class D multicast range"],
    ["240.0.0.0/4", "Reserved", "Reserved for future use"],
    ["255.255.255.255/32", "Limited Broadcast", "Local network broadcast"],
  ];

  const PRIVATE_RANGES_INFO_V6 = [
    ["::1/128", "Loopback", "Localhost"],
    ["::/128", "Unspecified", "All-zeros address"],
    ["::ffff:0:0/96", "IPv4-mapped", "Embeds an IPv4 address"],
    ["fc00::/7", "Unique Local (ULA)", "RFC 4193 — private IPv6 addressing"],
    ["fe80::/10", "Link-Local", "Not routable beyond the local link"],
    ["ff00::/8", "Multicast", "IPv6 multicast range"],
    ["2001:db8::/32", "Documentation", "Reserved for examples/docs"],
    ["2000::/3", "Global Unicast", "Publicly routable address space"],
  ];

  // ------------------------------------------------------ Reusable UI panel
  // Wires up a "IP Address [/CIDR] + mask select + Calculate" input group
  // that several pages need (the full IPv4 calculator page, and the compact
  // "base network" prompt on the splitter / VLSM pages). Handles the mask
  // <select> options, Enter-to-calculate, optional ?ip= URL sync, and calls
  // back with the computed info (or null on a parse error, after showing it).
  function setupIPv4Panel(cfg) {
    const ipInput = document.getElementById(cfg.ipInputId);
    const maskSelect = document.getElementById(cfg.maskSelectId);
    const calcBtn = document.getElementById(cfg.calcBtnId);
    const errorEl = cfg.errorId ? document.getElementById(cfg.errorId) : null;

    for (let prefix = 0; prefix <= 32; prefix++) {
      const opt = document.createElement("option");
      opt.value = String(prefix);
      opt.textContent = `/${prefix}  -  ${intToIp(prefixToMaskInt(prefix))}`;
      if (prefix === (cfg.defaultPrefix || 24)) opt.selected = true;
      maskSelect.appendChild(opt);
    }

    function parseInput() {
      const raw = ipInput.value.trim();
      if (!raw) return { error: "Please enter an IP address." };
      if (raw.includes("/")) {
        const [ipStr, cidrStr] = raw.split("/");
        const ipInt = ipToInt(ipStr);
        if (ipInt === null) return { error: `'${ipStr.trim()}' is not a valid IPv4 address.` };
        if (!/^\d{1,2}$/.test(cidrStr.trim())) return { error: `'${cidrStr.trim()}' is not a valid CIDR prefix.` };
        const prefix = parseInt(cidrStr.trim(), 10);
        if (prefix < 0 || prefix > 32) return { error: "CIDR prefix must be between 0 and 32." };
        return { ip: ipInt, prefix };
      }
      const ipInt = ipToInt(raw);
      if (ipInt === null) return { error: `'${raw}' is not a valid IPv4 address.` };
      const prefix = parseInt(maskSelect.value, 10);
      if (Number.isNaN(prefix)) return { error: "Select a subnet mask or provide a CIDR prefix." };
      return { ip: ipInt, prefix };
    }

    let currentInfo = null;

    function buildShareUrl() {
      const raw = ipInput.value.trim();
      const url = new URL(location.href);
      url.search = "";
      if (raw) url.searchParams.set("ip", raw);
      return url.toString();
    }

    function calculate() {
      if (errorEl) showError(errorEl, "");
      const parsed = parseInput();
      if (parsed.error) {
        if (errorEl) showError(errorEl, parsed.error);
        currentInfo = null;
        if (cfg.onResult) cfg.onResult(null);
        return null;
      }
      currentInfo = computeFields(parsed.ip, parsed.prefix);
      if (cfg.enableShareUrl) {
        try { history.replaceState(null, "", buildShareUrl()); } catch (e) { /* sandboxed context */ }
      }
      if (cfg.onResult) cfg.onResult(currentInfo);
      return currentInfo;
    }

    calcBtn.addEventListener("click", calculate);
    ipInput.addEventListener("keydown", (e) => { if (e.key === "Enter") calculate(); });
    maskSelect.addEventListener("change", calculate);

    if (cfg.readUrlParam) {
      const initParams = new URLSearchParams(location.search);
      if (initParams.get("ip")) ipInput.value = initParams.get("ip");
    }

    if (cfg.autoCalculate !== false) calculate();

    return {
      getInfo: () => currentInfo,
      calculate,
      buildShareUrl,
    };
  }

  global.SubnetTools = {
    MAX_SPLIT_ROWS, MAX_VISUAL_ROWS,
    ipToInt, intToIp, prefixToMaskInt, maskToPrefix, toBinaryOctets, ipClass, isPrivateIp, bitLength,
    expandIPv6, ipv6ToBigInt, bigIntToHextets, compressIPv6, v6PrefixMask, parseV6Cidr, ipv6Type,
    showError, showToast, copyText, renderRowsWithCopy, fillRefTable,
    parseNetworkString, computeFields, computeV6Fields,
    parseVlsmInput, vlsmPlan,
    PRIVATE_RANGES_INFO_V4, PRIVATE_RANGES_INFO_V6,
    setupIPv4Panel,
  };
})(window);
