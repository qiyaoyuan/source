/*
 * Agent Automation Detection Lab
 * 针对 X5Use AgentRuntime（chrome.debugger + puppeteer-core ExtensionTransport + CDP）
 * 与业界通用自动化检测手段的全覆盖检测页。
 * 所有数据仅保存在当前页面，不上传。
 */
(function () {
  "use strict";

  /* ================================================================
   * 0. 工具函数
   * ================================================================ */
  function hashString(input) {
    var hash = 2166136261;
    var text = String(input);
    for (var i = 0; i < text.length; i += 1) {
      hash ^= text.charCodeAt(i);
      hash = Math.imul(hash, 16777619);
    }
    return ("00000000" + (hash >>> 0).toString(16)).slice(-8);
  }

  function safe(label, fn, fallback) {
    try {
      return fn();
    } catch (error) {
      return fallback !== undefined ? fallback : {
        error: label + ": " + (error && error.message ? error.message : String(error))
      };
    }
  }

  function escapeHtml(value) {
    return String(value)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  function stddev(values) {
    if (!values.length) { return 0; }
    var mean = values.reduce(function (s, v) { return s + v; }, 0) / values.length;
    var variance = values.reduce(function (s, v) { return s + Math.pow(v - mean, 2); }, 0) / values.length;
    return Math.sqrt(variance);
  }

  function mean(values) {
    if (!values.length) { return 0; }
    return values.reduce(function (s, v) { return s + v; }, 0) / values.length;
  }

  function distance(x1, y1, x2, y2) {
    return Math.sqrt(Math.pow(x1 - x2, 2) + Math.pow(y1 - y2, 2));
  }

  function pushLimited(list, item, limit) {
    list.push(item);
    if (list.length > limit) { list.shift(); }
  }

  function probeOf(target) {
    if (!target || !target.closest) { return null; }
    var el = target.closest("[data-probe]");
    return el ? el.getAttribute("data-probe") : null;
  }

  function targetLabel(target) {
    if (!target || !target.tagName) { return "window"; }
    var label = target.tagName.toLowerCase();
    if (target.id) { label += "#" + target.id; }
    var probe = probeOf(target);
    if (probe) { label += "[data-probe=" + probe + "]"; }
    return label;
  }

  /* ================================================================
   * 1. 全局状态
   * ================================================================ */
  var startedAt = performance.now();
  var lastReport = null;

  /** 全量交互事件环（供分析） */
  var events = [];
  var EVENT_LIMIT = 1500;

  /** 行为统计计数 */
  var behavior = {
    moves: 0, clicks: 0, wheels: 0, scrolls: 0, keydowns: 0,
    paste: 0, visibilityChanges: 0, firstInteractionAt: null,
    untrustedEvents: 0,
    untrustedByType: {},
    resizes: []
  };

  /** AgentRuntime 痕迹（MutationObserver 捕获） */
  var traceLog = [];

  /** 静默 value 变更（无 input 事件的 JS 赋值） */
  var silentValueMutations = [];
  var lastKnownValues = {};

  /** CDP 探针累计状态 */
  var cdpProbe = {
    consoleGetterHit: 0,
    errorStackGetterHit: 0,
    toJsonHit: 0,
    lastRunAt: 0,
    debuggerSamples: []
  };

  /** 内核对抗回归验证状态（commit f98b861a / 9eef07f0） */
  var antiFp = {
    webdriverSamples: [],
    webdriverFlip: false,
    exceptionGetterHit: 0,
    exceptionToStringHit: 0,
    exceptionProbeAt: 0,
    worker: null
  };

  var speechVoicesCount = null;

  function markInteraction() {
    if (behavior.firstInteractionAt === null) {
      behavior.firstInteractionAt = Math.round(performance.now() - startedAt);
    }
  }

  /* ================================================================
   * 2. AgentRuntime 痕迹监视（MutationObserver）
   *    - data-hi="N"        : getState 高亮元素索引注入
   *    - data-__cdp-locate  : CDP 定位瞬态属性
   *    - data-x5-overlay    : 蒙层节点
   *    - #playwright-highlight-container / #x5-overlay-* : 节点创建
   * ================================================================ */
  var TRACE_ATTRS = ["data-hi", "data-__cdp-locate", "data-x5-overlay"];
  var TRACE_NODE_RE = /playwright-highlight-container|x5-overlay/i;

  function addTrace(kind, detail) {
    pushLimited(traceLog, {
      t: Math.round(performance.now() - startedAt),
      kind: kind,
      detail: detail
    }, 200);
    scheduleDetection();
    renderTrace();
  }

  function describeNode(node) {
    if (!node || !node.tagName) { return String(node && node.nodeName); }
    var s = node.tagName.toLowerCase();
    if (node.id) { s += "#" + node.id; }
    if (typeof node.className === "string" && node.className) {
      s += "." + node.className.trim().split(/\s+/).slice(0, 3).join(".");
    }
    var text = (node.textContent || "").trim().slice(0, 40);
    if (text) { s += ' "' + text + '"'; }
    return s;
  }

  function sweepExistingMarkers() {
    safe("markerSweep", function () {
      document.querySelectorAll("[data-hi]").forEach(function (el) {
        addTrace("data-hi-present", describeNode(el) + " data-hi=" + el.getAttribute("data-hi"));
      });
      document.querySelectorAll("[data-__cdp-locate]").forEach(function (el) {
        addTrace("cdp-locate-present", describeNode(el));
      });
      document.querySelectorAll("[data-x5-overlay], #x5-overlay-root, #playwright-highlight-container").forEach(function (el) {
        addTrace("marker-node-present", describeNode(el));
      });
    });
  }

  function startTraceObserver() {
    if (!document.documentElement || !window.MutationObserver) { return; }
    var observer = new MutationObserver(function (mutations) {
      mutations.forEach(function (m) {
        if (m.type === "attributes") {
          var attr = m.attributeName;
          var value = m.target.getAttribute(attr);
          addTrace("attr:" + attr,
            (value === null ? "removed" : "set=" + value) + " on " + describeNode(m.target));
        } else if (m.type === "childList") {
          Array.prototype.forEach.call(m.addedNodes, function (node) {
            if (node.nodeType !== 1) { return; }
            var hit = TRACE_NODE_RE.test(node.id || "") || TRACE_NODE_RE.test(String(node.className || ""));
            if (!hit && node.querySelector) {
              hit = !!node.querySelector("#playwright-highlight-container, [id^=x5-overlay], [data-x5-overlay]");
            }
            if (hit) { addTrace("node-added", describeNode(node)); }
          });
          Array.prototype.forEach.call(m.removedNodes, function (node) {
            if (node.nodeType !== 1) { return; }
            if (TRACE_NODE_RE.test(node.id || "") || TRACE_NODE_RE.test(String(node.className || ""))) {
              addTrace("node-removed", describeNode(node));
            }
          });
        }
      });
    });
    observer.observe(document.documentElement, {
      subtree: true,
      childList: true,
      attributes: true,
      attributeFilter: TRACE_ATTRS
    });
  }

  /* ================================================================
   * 3. 交互事件捕获（事件保真度分析原始数据）
   * ================================================================ */
  var POINTER_TYPES = {
    pointerover: 1, pointermove: 1, pointerdown: 1, pointerup: 1,
    mouseover: 1, mousemove: 1, mousedown: 1, mouseup: 1,
    click: 1, dblclick: 1, contextmenu: 1, wheel: 1
  };
  var KEY_TYPES = { keydown: 1, keypress: 1, keyup: 1 };
  var INPUT_TYPES = { beforeinput: 1, input: 1, change: 1, compositionstart: 1, compositionend: 1 };
  var DRAG_TYPES = { dragstart: 1, dragenter: 1, dragover: 1, dragleave: 1, drop: 1, dragend: 1 };
  var OTHER_TYPES = {
    scroll: 1, focusin: 1, focusout: 1, paste: 1, copy: 1,
    touchstart: 1, touchmove: 1, touchend: 1
  };

  function recordEvent(type, e) {
    var entry = {
      t: Math.round(performance.now() - startedAt),
      type: type,
      trusted: e.isTrusted !== false,
      probe: probeOf(e.target),
      target: targetLabel(e.target)
    };

    if (POINTER_TYPES[type]) {
      entry.x = typeof e.clientX === "number" ? Math.round(e.clientX * 100) / 100 : null;
      entry.y = typeof e.clientY === "number" ? Math.round(e.clientY * 100) / 100 : null;
      entry.button = e.button;
      entry.buttons = e.buttons;
      entry.detail = e.detail;
      if (type === "pointermove" && e.getCoalescedEvents) {
        entry.coalesced = safe("coalesced", function () { return e.getCoalescedEvents().length; }, null);
      }
      if (type === "mousemove" || type === "pointermove") {
        entry.movementX = e.movementX;
        entry.movementY = e.movementY;
      }
      if (type === "wheel") {
        entry.deltaY = e.deltaY;
        entry.deltaMode = e.deltaMode;
      }
      if (type === "click" && e.target && e.target.getBoundingClientRect) {
        var rect = e.target.getBoundingClientRect();
        if (rect.width > 0 && rect.height > 0) {
          var cx = rect.left + rect.width / 2;
          var cy = rect.top + rect.height / 2;
          entry.centerDistanceRatio = Number(
            (distance(e.clientX, e.clientY, cx, cy) / Math.max(1, Math.min(rect.width, rect.height))).toFixed(3)
          );
          entry.centerDistancePx = Number(distance(e.clientX, e.clientY, cx, cy).toFixed(2));
        }
      }
    }
    if (KEY_TYPES[type]) {
      entry.key = e.key;
      entry.code = e.code;
      entry.repeat = e.repeat;
    }
    if (INPUT_TYPES[type]) {
      entry.inputType = e.inputType;
      entry.data = typeof e.data === "string" ? e.data.slice(0, 16) : null;
    }
    if (type === "scroll" && e.target && e.target !== document && e.target.scrollTop !== undefined) {
      entry.scrollTop = Math.round(e.target.scrollTop);
    }

    pushLimited(events, entry, EVENT_LIMIT);

    // 计数
    if (!entry.trusted) {
      behavior.untrustedEvents += 1;
      behavior.untrustedByType[type] = (behavior.untrustedByType[type] || 0) + 1;
    }
    if (type === "pointermove" || type === "mousemove") { behavior.moves += 1; markInteraction(); }
    if (type === "click") { behavior.clicks += 1; markInteraction(); }
    if (type === "wheel") { behavior.wheels += 1; markInteraction(); }
    if (type === "scroll") { behavior.scrolls += 1; markInteraction(); }
    if (type === "keydown") { behavior.keydowns += 1; markInteraction(); }
    if (type === "paste") { behavior.paste += 1; markInteraction(); }

    if (type === "input" || type === "change") {
      var p = entry.probe;
      if (p && e.target && "value" in e.target) { lastKnownValues[p] = e.target.value; }
    }
  }

  var CAPTURE_LIST = Object.keys(POINTER_TYPES)
    .concat(Object.keys(KEY_TYPES), Object.keys(INPUT_TYPES), Object.keys(DRAG_TYPES), Object.keys(OTHER_TYPES));

  function startEventCapture() {
    CAPTURE_LIST.forEach(function (type) {
      var opts = { capture: true, passive: true };
      window.addEventListener(type, function (e) { recordEvent(type, e); }, opts);
    });
    document.addEventListener("visibilitychange", function () {
      behavior.visibilityChanges += 1;
    });
    window.addEventListener("resize", function () {
      pushLimited(behavior.resizes, {
        t: Math.round(performance.now() - startedAt),
        innerWidth: window.innerWidth,
        innerHeight: window.innerHeight,
        outerWidth: window.outerWidth,
        outerHeight: window.outerHeight
      }, 50);
    });
    // 输入控件 value 轮询：识别"无 input 事件的 JS 赋值"（input_text 静默清空）
    setInterval(function () {
      ["textInput", "textArea"].forEach(function (probe) {
        var el = document.querySelector('[data-probe="' + probe + '"]');
        if (!el) { return; }
        var current = el.value;
        if (!(probe in lastKnownValues)) { lastKnownValues[probe] = current; return; }
        if (current !== lastKnownValues[probe]) {
          var recentInput = events.some(function (ev) {
            return ev.probe === probe && (ev.type === "input" || ev.type === "change") &&
              (performance.now() - startedAt - ev.t) < 600;
          });
          if (!recentInput) {
            pushLimited(silentValueMutations, {
              t: Math.round(performance.now() - startedAt),
              probe: probe,
              from: String(lastKnownValues[probe]).slice(0, 20),
              to: String(current).slice(0, 20)
            }, 50);
          }
          lastKnownValues[probe] = current;
        }
      });

      // webdriver 运行期翻转监控（回归 commit f98b861a：spoof 应在进程内稳定，不应抖动）
      var wd = safe("webdriverSample", function () { return navigator.webdriver; }, null);
      var last = antiFp.webdriverSamples.length ? antiFp.webdriverSamples[antiFp.webdriverSamples.length - 1].value : null;
      if (antiFp.webdriverSamples.length && wd !== last) {
        antiFp.webdriverFlip = true;
        addTrace("webdriver-flip", "navigator.webdriver 运行期变化: " + last + " -> " + wd);
      }
      pushLimited(antiFp.webdriverSamples, { t: Math.round(performance.now() - startedAt), value: wd }, 200);
    }, 500);
  }

  /* ================================================================
   * 4. 事件序列查询辅助
   * ================================================================ */
  function eventsOf(probe, types) {
    return events.filter(function (ev) {
      return ev.probe === probe && types.indexOf(ev.type) !== -1;
    });
  }

  function lastEventBefore(probe, types, t, maxAgeMs) {
    for (var i = events.length - 1; i >= 0; i -= 1) {
      var ev = events[i];
      if (ev.t > t) { continue; }
      if (maxAgeMs && t - ev.t > maxAgeMs) { return null; }
      if (ev.probe === probe && types.indexOf(ev.type) !== -1) { return ev; }
    }
    return null;
  }

  function anyEventBefore(types, t, maxAgeMs) {
    for (var i = events.length - 1; i >= 0; i -= 1) {
      var ev = events[i];
      if (maxAgeMs && t - ev.t > maxAgeMs) { return false; }
      if (types.indexOf(ev.type) !== -1) { return true; }
    }
    return false;
  }

  /* ================================================================
   * 5. 靶场逐目标判定（verdict）
   * ================================================================ */
  function verdict(level, text) { return { level: level, text: text }; }

  function analyzeClickProbe(probe) {
    var out = [];
    var clicks = eventsOf(probe, ["click"]);
    if (!clicks.length) { return out; }
    clicks.forEach(function (c) {
      if (!c.trusted) {
        out.push(verdict("danger", "click isTrusted=false：JS 合成点击（AgentRuntime JS 降级路径）"));
        return;
      }
      var approach = lastEventBefore(probe, ["pointermove", "mousemove", "mouseover", "pointerover"], c.t, 1500);
      if (!approach) {
        out.push(verdict("warn", "点击前 1.5s 内无指针轨迹（瞬移点击，CDP dispatchMouseEvent 特征）"));
      }
      if (c.centerDistancePx !== undefined && c.centerDistancePx !== null && c.centerDistancePx < 1) {
        out.push(verdict("warn", "落点距元素几何中心 " + c.centerDistancePx + "px（CDP 中心点点击特征）"));
      } else if (c.centerDistanceRatio !== undefined && c.centerDistanceRatio !== null && c.centerDistanceRatio < 0.05) {
        out.push(verdict("info", "落点接近元素中心（ratio=" + c.centerDistanceRatio + "）"));
      }
      var down = lastEventBefore(probe, ["pointerdown", "mousedown"], c.t, 200);
      if (down && !down.trusted) {
        out.push(verdict("warn", "mousedown/pointerdown isTrusted=false"));
      }
    });
    return out.slice(-4);
  }

  function analyzeDblclickProbe(probe) {
    var out = [];
    var dbls = eventsOf(probe, ["dblclick"]);
    var clicks = eventsOf(probe, ["click"]);
    dbls.forEach(function (d) {
      if (!d.trusted) {
        out.push(verdict("danger", "dblclick isTrusted=false：JS 合成双击（AgentRuntime 降级路径）"));
      }
    });
    if (clicks.length >= 2) {
      var a = clicks[clicks.length - 2];
      var b = clicks[clicks.length - 1];
      if (a.x !== null && b.x !== null && a.x === b.x && a.y === b.y) {
        out.push(verdict("warn", "两次点击坐标完全一致 (" + a.x + "," + a.y + ")"));
      }
      var gap = b.t - a.t;
      if (gap < 60) {
        out.push(verdict("info", "双击间隔 " + gap + "ms（低于多数真人双击）"));
      }
    }
    return out.slice(-4);
  }

  function analyzeHoverProbe(probe) {
    var out = [];
    var hovers = eventsOf(probe, ["mouseover", "pointerover"]);
    hovers.forEach(function (h) {
      if (!h.trusted) {
        out.push(verdict("danger", h.type + " isTrusted=false：JS dispatchEvent 悬停（hover_element 主路径）"));
      }
    });
    var moves = eventsOf(probe, ["pointermove", "mousemove"]);
    if (hovers.length && !moves.length) {
      out.push(verdict("warn", "有 hover 事件但无任何指针移动（无真实悬停过程）"));
    }
    return out.slice(-4);
  }

  function analyzeInputProbe(probe) {
    var out = [];
    var keys = eventsOf(probe, ["keydown"]);
    var inputs = eventsOf(probe, ["input"]);
    var focusins = eventsOf(probe, ["focusin"]);

    focusins.forEach(function (f) {
      if (!f.trusted) {
        out.push(verdict("danger", "focusin isTrusted=false：JS focus()（focus_element 路径）"));
        return;
      }
      var pre = lastEventBefore(probe, ["pointerdown", "mousedown", "keydown"], f.t, 1200);
      if (!pre) {
        out.push(verdict("warn", "focus 前无 pointerdown/Tab（JS 或 CDP 直接聚焦）"));
      }
    });

    if (keys.length >= 6) {
      var intervals = [];
      for (var i = 1; i < keys.length; i += 1) { intervals.push(keys[i].t - keys[i - 1].t); }
      var sd = stddev(intervals);
      var avg = mean(intervals);
      if (avg >= 3 && avg <= 8 && sd < 3) {
        out.push(verdict("warn", "击键间隔均值 " + avg.toFixed(1) + "ms / 方差≈" + sd.toFixed(1) +
          "（固定节拍，AgentRuntime input_text delay:5ms 特征）"));
      } else if (sd > 0 && sd < 10 && avg < 60) {
        out.push(verdict("warn", "击键节奏过于稳定（avg " + Math.round(avg) + "ms, stddev " + sd.toFixed(1) + "）"));
      }
      var repeats = keys.filter(function (k) { return k.repeat; }).length;
      if (repeats > 0) {
        out.push(verdict("info", "检测到 " + repeats + " 次长按自动重复（真实键盘特征）"));
      }
    }

    inputs.forEach(function (inp) {
      if (!inp.trusted) {
        out.push(verdict("danger", "input isTrusted=false：JS dispatchEvent 输入"));
        return;
      }
      var preKey = lastEventBefore(probe, ["keydown", "keypress", "compositionstart"], inp.t, 400);
      if (!preKey && inp.inputType && inp.inputType.indexOf("insert") === 0) {
        out.push(verdict("warn", "input(" + inp.inputType + ") 前 400ms 无任何按键事件（CDP Input.insertText 特征）"));
      }
    });

    var silent = silentValueMutations.filter(function (m) { return m.probe === probe; });
    if (silent.length) {
      out.push(verdict("danger", "value 被静默改写 " + silent.length + " 次（无 input 事件的 JS 赋值，input_text 清空路径）"));
    }
    return out.slice(-5);
  }

  function analyzeSelectProbe(probe) {
    var out = [];
    eventsOf(probe, ["change"]).forEach(function (c) {
      if (!c.trusted) {
        out.push(verdict("danger", "change isTrusted=false：JS 直改 selected + dispatch（select_dropdown_option 路径）"));
        return;
      }
      var pre = lastEventBefore(probe, ["pointerdown", "mousedown", "keydown", "click"], c.t, 1500);
      if (!pre) {
        out.push(verdict("warn", "change 前无点击/按键（非用户操作路径）"));
      }
    });
    return out.slice(-4);
  }

  function analyzeCheckProbe(probe) {
    var out = [];
    eventsOf(probe, ["click"]).forEach(function (c) {
      if (!c.trusted) {
        out.push(verdict("danger", "click isTrusted=false：JS el.click()（check_op 路径）"));
        return;
      }
      var pre = lastEventBefore(probe, ["pointerdown", "mousedown", "keydown"], c.t, 300);
      if (!pre) {
        out.push(verdict("warn", "checkbox click 前无 pointerdown/keydown"));
      }
    });
    return out.slice(-4);
  }

  function analyzeScrollProbe(probe) {
    var out = [];
    var scrolls = eventsOf(probe, ["scroll"]);
    scrolls.forEach(function (s) {
      var preWheel = anyEventBefore(["wheel", "touchmove", "keydown"], s.t, 800);
      if (!preWheel) {
        out.push(verdict("warn", "scroll 前 800ms 无 wheel/touch/key 前驱（JS scrollBy/scrollTo，AgentRuntime scroll_* 路径）"));
      }
    });
    eventsOf(probe, ["wheel"]).forEach(function (w) {
      if (!w.trusted) {
        out.push(verdict("warn", "wheel isTrusted=false：JS 合成滚轮"));
      }
    });
    return out.slice(-4);
  }

  function analyzeDragProbe(probe) {
    var out = [];
    eventsOf(probe, ["dragstart", "drop", "dragend"]).forEach(function (d) {
      if (!d.trusted) {
        out.push(verdict("danger", d.type + " isTrusted=false：JS 合成 DragEvent（drag_drop HTML5 路径）"));
      }
    });
    return out.slice(-4);
  }

  var PROBE_ANALYZERS = {
    btnA: analyzeClickProbe,
    btnB: analyzeClickProbe,
    dblPad: analyzeDblclickProbe,
    hoverPad: analyzeHoverProbe,
    textInput: analyzeInputProbe,
    textArea: analyzeInputProbe,
    selectBox: analyzeSelectProbe,
    checkBox: analyzeCheckProbe,
    scrollPad: analyzeScrollProbe,
    dragSrc: analyzeDragProbe
  };

  function computeVerdicts() {
    var result = {};
    Object.keys(PROBE_ANALYZERS).forEach(function (probe) {
      result[probe] = PROBE_ANALYZERS[probe](probe);
    });
    return result;
  }

  /* ================================================================
   * 6. 静态环境探针
   * ================================================================ */
  function getNavigatorData() {
    var webdriverDesc = safe("webdriverDesc", function () {
      return Object.getOwnPropertyDescriptor(Navigator.prototype, "webdriver") ||
        Object.getOwnPropertyDescriptor(navigator, "webdriver") || null;
    }, null);
    return {
      userAgent: navigator.userAgent,
      platform: navigator.platform,
      vendor: navigator.vendor,
      webdriver: navigator.webdriver,
      webdriverDescriptor: webdriverDesc ? {
        onPrototype: !!Object.getOwnPropertyDescriptor(Navigator.prototype, "webdriver"),
        hasGetter: !!webdriverDesc.get,
        configurable: webdriverDesc.configurable
      } : null,
      languages: navigator.languages ? Array.prototype.slice.call(navigator.languages) : [],
      language: navigator.language,
      hardwareConcurrency: navigator.hardwareConcurrency,
      deviceMemory: navigator.deviceMemory,
      maxTouchPoints: navigator.maxTouchPoints,
      cookieEnabled: navigator.cookieEnabled,
      pluginsLength: navigator.plugins ? navigator.plugins.length : null,
      mimeTypesLength: navigator.mimeTypes ? navigator.mimeTypes.length : null,
      pdfViewerEnabled: navigator.pdfViewerEnabled,
      userAgentData: navigator.userAgentData ? {
        brands: navigator.userAgentData.brands,
        mobile: navigator.userAgentData.mobile,
        platform: navigator.userAgentData.platform
      } : null
    };
  }

  function getHighEntropyValues() {
    if (!navigator.userAgentData || !navigator.userAgentData.getHighEntropyValues) {
      return Promise.resolve(null);
    }
    return navigator.userAgentData.getHighEntropyValues([
      "architecture", "bitness", "model", "platform", "platformVersion",
      "uaFullVersion", "fullVersionList", "wow64"
    ]).catch(function (error) { return { error: error.message }; });
  }

  function getEnvironmentData() {
    return {
      screen: {
        width: screen.width, height: screen.height,
        availWidth: screen.availWidth, availHeight: screen.availHeight,
        colorDepth: screen.colorDepth, pixelDepth: screen.pixelDepth
      },
      viewport: {
        innerWidth: window.innerWidth, innerHeight: window.innerHeight,
        outerWidth: window.outerWidth, outerHeight: window.outerHeight,
        devicePixelRatio: window.devicePixelRatio
      },
      locale: {
        timezone: Intl.DateTimeFormat().resolvedOptions().timeZone,
        calendar: Intl.DateTimeFormat().resolvedOptions().calendar,
        numberingSystem: Intl.DateTimeFormat().resolvedOptions().numberingSystem
      },
      mediaQueries: safe("mediaQueries", function () {
        function mq(q) { return window.matchMedia(q).matches; }
        return {
          pointerFine: mq("(pointer: fine)"),
          pointerCoarse: mq("(pointer: coarse)"),
          anyPointer: mq("(any-pointer: fine)"),
          hover: mq("(hover: hover)"),
          anyHover: mq("(any-hover: hover)"),
          colorGamutSrgb: mq("(color-gamut: srgb)"),
          prefersReducedMotion: mq("(prefers-reduced-motion: reduce)")
        };
      }, null),
      chromeObject: {
        present: Boolean(window.chrome),
        keys: window.chrome ? Object.keys(window.chrome).slice(0, 20) : [],
        hasRuntime: Boolean(window.chrome && window.chrome.runtime)
      },
      visibility: {
        visibilityState: document.visibilityState,
        hidden: document.hidden,
        hasFocus: safe("hasFocus", function () { return document.hasFocus(); }, null)
      },
      connection: safe("connection", function () {
        if (!navigator.connection) { return null; }
        return {
          effectiveType: navigator.connection.effectiveType,
          rtt: navigator.connection.rtt,
          downlink: navigator.connection.downlink,
          saveData: navigator.connection.saveData
        };
      }, null)
    };
  }

  function getCanvasHash() {
    return safe("canvas", function () {
      var canvas = document.createElement("canvas");
      canvas.width = 240;
      canvas.height = 80;
      var ctx = canvas.getContext("2d");
      ctx.textBaseline = "top";
      ctx.fillStyle = "#f3f4f6";
      ctx.fillRect(0, 0, 240, 80);
      ctx.fillStyle = "#0f766e";
      ctx.font = "18px Arial";
      ctx.fillText("Automation Detection 123", 8, 8);
      ctx.strokeStyle = "#b45309";
      ctx.beginPath();
      ctx.arc(190, 42, 22, 0, Math.PI * 2);
      ctx.stroke();
      return hashString(canvas.toDataURL());
    }, null);
  }

  function getWebglInfo() {
    return safe("webgl", function () {
      var canvas = document.createElement("canvas");
      var gl = canvas.getContext("webgl") || canvas.getContext("experimental-webgl");
      if (!gl) { return { supported: false }; }
      var debug = gl.getExtension("WEBGL_debug_renderer_info");
      var vendor = debug ? gl.getParameter(debug.UNMASKED_VENDOR_WEBGL) : gl.getParameter(gl.VENDOR);
      var renderer = debug ? gl.getParameter(debug.UNMASKED_RENDERER_WEBGL) : gl.getParameter(gl.RENDERER);
      return {
        supported: true,
        vendor: vendor,
        renderer: renderer,
        version: gl.getParameter(gl.VERSION),
        shadingLanguageVersion: gl.getParameter(gl.SHADING_LANGUAGE_VERSION),
        maxTextureSize: gl.getParameter(gl.MAX_TEXTURE_SIZE),
        extensionCount: gl.getSupportedExtensions() ? gl.getSupportedExtensions().length : 0
      };
    }, { supported: false });
  }

  function getAudioHash() {
    return safe("audio", function () {
      var AudioCtx = window.OfflineAudioContext || window.webkitOfflineAudioContext;
      if (!AudioCtx) { return Promise.resolve(null); }
      var context = new AudioCtx(1, 4410, 44100);
      var oscillator = context.createOscillator();
      var compressor = context.createDynamicsCompressor();
      oscillator.type = "triangle";
      oscillator.frequency.value = 10000;
      compressor.threshold.value = -50;
      compressor.knee.value = 40;
      compressor.ratio.value = 12;
      compressor.attack.value = 0;
      compressor.release.value = 0.25;
      oscillator.connect(compressor);
      compressor.connect(context.destination);
      oscillator.start(0);
      return context.startRendering().then(function (buffer) {
        var data = buffer.getChannelData(0).slice(450, 650);
        return hashString(Array.prototype.join.call(data, ","));
      }).catch(function () { return null; });
    }, Promise.resolve(null));
  }

  function getAutomationGlobals() {
    var names = [
      "__webdriver_evaluate", "__selenium_evaluate", "__webdriver_script_function",
      "__webdriver_script_func", "__webdriver_script_fn", "__fxdriver_evaluate",
      "__driver_unwrapped", "__webdriver_unwrapped", "__selenium_unwrapped",
      "__fxdriver_unwrapped", "_Selenium_IDE_Recorder", "_selenium", "callSelenium",
      "_phantom", "phantom", "domAutomation", "domAutomationController",
      "__playwright", "__playwright__binding__", "__puppeteer_utility_world__",
      "cdc_adoQpoasnfa76pfcZLmcfl_Array", "cdc_adoQpoasnfa76pfcZLmcfl_Promise",
      "cdc_adoQpoasnfa76pfcZLmcfl_Symbol"
    ];
    var docKeys = names.filter(function (n) { return n in window || n in document; });
    var cdcKeys = safe("cdcKeys", function () {
      return Object.keys(document).filter(function (k) { return k.indexOf("cdc_") === 0; })
        .concat(Object.keys(window).filter(function (k) { return k.indexOf("cdc_") === 0; }));
    }, []);
    return docKeys.concat(cdcKeys);
  }

  function getNativeIntegrity() {
    return safe("nativeIntegrity", function () {
      var targets = [
        ["permissions.query", navigator.permissions && navigator.permissions.query],
        ["canvas.toDataURL", HTMLCanvasElement.prototype.toDataURL],
        ["webgl.getParameter", window.WebGLRenderingContext && WebGLRenderingContext.prototype.getParameter],
        ["element.click", HTMLElement.prototype.click],
        ["element.dispatchEvent", EventTarget.prototype.dispatchEvent],
        ["function.toString", Function.prototype.toString],
        ["console.log", console.log]
      ];
      return targets.map(function (pair) {
        if (!pair[1]) { return { name: pair[0], nativeLike: null, hash: null }; }
        var source = Function.prototype.toString.call(pair[1]);
        return {
          name: pair[0],
          nativeLike: source.indexOf("[native code]") !== -1,
          hash: hashString(source)
        };
      });
    }, []);
  }

  function getIframeConsistency() {
    return safe("iframeConsistency", function () {
      var iframe = document.createElement("iframe");
      iframe.setAttribute("title", "clean realm probe");
      iframe.style.display = "none";
      document.body.appendChild(iframe);
      var fw = iframe.contentWindow;
      var result = {
        webdriverSame: navigator.webdriver === fw.navigator.webdriver,
        languagesSame: JSON.stringify(navigator.languages) === JSON.stringify(fw.navigator.languages),
        chromeSamePresence: Boolean(window.chrome) === Boolean(fw.chrome),
        permissionsQuerySameSource: null,
        clickSameSource: null,
        toStringSameSource: null,
        webdriverDescriptor: Object.getOwnPropertyDescriptor(Navigator.prototype, "webdriver") ? "prototype" :
          (Object.getOwnPropertyDescriptor(navigator, "webdriver") ? "own" : "missing")
      };
      if (navigator.permissions && fw.navigator.permissions) {
        result.permissionsQuerySameSource =
          Function.prototype.toString.call(navigator.permissions.query) ===
          fw.Function.prototype.toString.call(fw.navigator.permissions.query);
      }
      result.clickSameSource =
        Function.prototype.toString.call(HTMLElement.prototype.click) ===
        fw.Function.prototype.toString.call(fw.HTMLElement.prototype.click);
      result.toStringSameSource =
        Function.prototype.toString.call(Function.prototype.toString) ===
        fw.Function.prototype.toString.call(fw.Function.prototype.toString);
      iframe.remove();
      return result;
    }, null);
  }

  function getPermissionsConsistency() {
    if (!navigator.permissions || !navigator.permissions.query) {
      return Promise.resolve({ supported: false });
    }
    var checks = ["notifications", "geolocation", "camera", "microphone", "clipboard-read"].map(function (name) {
      return navigator.permissions.query({ name: name }).then(function (status) {
        return { name: name, state: status.state };
      }).catch(function (e) { return { name: name, error: e.message }; });
    });
    return Promise.all(checks).then(function (results) {
      var out = { supported: true, results: results };
      var notif = results.filter(function (r) { return r.name === "notifications"; })[0];
      out.notificationPermission = ("Notification" in window) ? Notification.permission : "no-api";
      if (notif && notif.state) {
        // 经典 headless 检测：query=prompt 但 Notification.permission=denied（反之亦然）
        out.notificationMismatch =
          (notif.state === "prompt" && out.notificationPermission === "denied") ||
          (notif.state === "denied" && out.notificationPermission === "default");
      }
      return out;
    }).catch(function (e) { return { supported: false, error: e.message }; });
  }

  function getMediaDevicesCount() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.enumerateDevices) {
      return Promise.resolve(null);
    }
    return navigator.mediaDevices.enumerateDevices().then(function (list) {
      return {
        total: list.length,
        audioinput: list.filter(function (d) { return d.kind === "audioinput"; }).length,
        videoinput: list.filter(function (d) { return d.kind === "videoinput"; }).length,
        audiooutput: list.filter(function (d) { return d.kind === "audiooutput"; }).length
      };
    }).catch(function () { return null; });
  }

  function getSpeechVoices() {
    return safe("speechVoices", function () {
      if (!window.speechSynthesis) { return { supported: false }; }
      var voices = window.speechSynthesis.getVoices();
      speechVoicesCount = voices.length;
      return { supported: true, count: voices.length };
    }, { supported: false });
  }

  /* ================================================================
   * 7. CDP / Debugger attach 探针
   * ================================================================ */
  function runCdpSerializationProbe() {
    return safe("cdpSerializationProbe", function () {
      cdpProbe.lastRunAt = Math.round(performance.now());

      var probeObject = {};
      Object.defineProperty(probeObject, "cdpGetterProbe", {
        get: function () {
          cdpProbe.consoleGetterHit += 1;
          return "getter-read";
        }
      });
      Object.defineProperty(probeObject, "toJSON", {
        value: function () {
          cdpProbe.toJsonHit += 1;
          return {};
        }
      });

      var error = new Error("cdp-stack-probe");
      Object.defineProperty(error, "stack", {
        get: function () {
          cdpProbe.errorStackGetterHit += 1;
          return "stack-read";
        }
      });

      console.debug("automation-detection-cdp-probe", probeObject, error);
      return {
        consoleGetterHit: cdpProbe.consoleGetterHit,
        errorStackGetterHit: cdpProbe.errorStackGetterHit,
        toJsonHit: cdpProbe.toJsonHit,
        lastRunAt: cdpProbe.lastRunAt,
        note: "Getter/toJSON hits happen when a CDP Runtime client requests console object previews."
      };
    }, {
      consoleGetterHit: cdpProbe.consoleGetterHit,
      errorStackGetterHit: cdpProbe.errorStackGetterHit,
      toJsonHit: cdpProbe.toJsonHit,
      note: "probe failed"
    });
  }

  function runDebuggerTimingProbe() {
    return safe("debuggerTimingProbe", function () {
      var samples = [];
      for (var i = 0; i < 3; i += 1) {
        var before = performance.now();
        // 测量已附加的 inspector 是否会在 debugger 语句上暂停
        debugger;
        samples.push(Number((performance.now() - before).toFixed(3)));
      }
      cdpProbe.debuggerSamples = samples;
      return {
        samplesMs: samples,
        maxMs: Math.max.apply(Math, samples),
        avgMs: Number(mean(samples).toFixed(3))
      };
    }, { samplesMs: [], maxMs: 0, avgMs: 0, error: "debugger timing probe failed" });
  }

  function getErrorStackProbe() {
    return safe("errorStackProbe", function () {
      var stack = new Error("automation-stack-probe").stack || "";
      var lines = stack.split("\n").map(function (l) { return l.trim(); }).filter(Boolean);
      var automationHints = lines.filter(function (line) {
        return /puppeteer|playwright|selenium|webdriver|__puppeteer|__playwright|ExecutionContext|Runtime\.evaluate|debugger eval/i.test(line);
      });
      return {
        lineCount: lines.length,
        firstLine: lines[0] || "",
        formatHash: hashString(lines.slice(0, 6).join("\n")),
        automationHints: automationHints.slice(0, 8),
        stackTraceLimit: Error.stackTraceLimit
      };
    }, { lineCount: 0, firstLine: "", formatHash: null, automationHints: [], error: "stack probe failed" });
  }

  /* ================================================================
   * 6.1 内核对抗回归探针（commit f98b861a webdriver 伪装 /
   *     commit 9eef07f0 V8 Runtime inspector 抑制）
   * ================================================================ */

  // Worker isolate 探针：commit 9eef07f0 声称覆盖每个 Worker isolate，
  // 在 Worker 内复跑 console getter / debugger 时序 / webdriver，验证无遗漏。
  function runWorkerProbe() {
    return safe("workerProbe", function () {
      if (!window.Worker || !window.Blob) { return Promise.resolve({ supported: false }); }
      var code = [
        'var hits = { getter: 0, stackGetter: 0 };',
        'var obj = {};',
        'Object.defineProperty(obj, "p", { get: function () { hits.getter += 1; return 1; } });',
        'var err = new Error("worker-stack-probe");',
        'Object.defineProperty(err, "stack", { get: function () { hits.stackGetter += 1; return "s"; } });',
        'console.debug("worker-cdp-probe", obj, err);',
        'var samples = [];',
        'for (var i = 0; i < 3; i += 1) {',
        '  var t0 = performance.now();',
        '  debugger;',
        '  samples.push(Number((performance.now() - t0).toFixed(3)));',
        '}',
        'postMessage({',
        '  supported: true,',
        '  consoleGetterHit: hits.getter,',
        '  errorStackGetterHit: hits.stackGetter,',
        '  debuggerMaxMs: Math.max.apply(Math, samples),',
        '  webdriver: ("webdriver" in navigator) ? navigator.webdriver : "property-absent",',
        '  userAgent: navigator.userAgent,',
        '  hardwareConcurrency: navigator.hardwareConcurrency,',
        '  languages: navigator.languages ? Array.prototype.slice.call(navigator.languages) : []',
        '});'
      ].join("\n");
      var worker = new Worker(URL.createObjectURL(new Blob([code], { type: "text/javascript" })));
      return new Promise(function (resolve) {
        var timer = setTimeout(function () {
          worker.terminate();
          resolve({ supported: true, timeout: true });
        }, 4000);
        worker.onmessage = function (e) {
          clearTimeout(timer);
          worker.terminate();
          resolve(e.data);
        };
        worker.onerror = function (e) {
          clearTimeout(timer);
          worker.terminate();
          resolve({ supported: true, error: e.message || "worker error" });
        };
      });
    }, Promise.resolve({ supported: false }));
  }

  // 异常序列化探针：console.debug 之外，Runtime.exceptionThrown 同样会触发
  // inspector 对异常对象做 preview 序列化。若 9eef07f0 只堵了 console 路径，
  // 这里仍会命中 getter。
  function runExceptionSerializationProbe() {
    return safe("exceptionSerializationProbe", function () {
      antiFp.exceptionProbeAt = Math.round(performance.now());
      var probe = { marker: "exception-serialization-probe" };
      Object.defineProperty(probe, "leakProp", {
        get: function () {
          antiFp.exceptionGetterHit += 1;
          return "leak";
        }
      });
      Object.defineProperty(probe, "toString", {
        value: function () {
          antiFp.exceptionToStringHit += 1;
          return "ExceptionProbe";
        }
      });
      // 异步 throw：走 Runtime.exceptionThrown，不被页面 catch
      setTimeout(function () { throw probe; }, 0);
      // Promise rejection 通道
      safe("exceptionReject", function () { Promise.reject(probe); });
      return {
        exceptionGetterHit: antiFp.exceptionGetterHit,
        exceptionToStringHit: antiFp.exceptionToStringHit,
        lastRunAt: antiFp.exceptionProbeAt,
        note: "Getter hits indicate the inspector is serializing uncaught exceptions (Runtime.exceptionThrown preview path)."
      };
    }, {
      exceptionGetterHit: antiFp.exceptionGetterHit,
      exceptionToStringHit: antiFp.exceptionToStringHit,
      lastRunAt: antiFp.exceptionProbeAt
    });
  }

  // webdriver 伪装回归：值 + 描述符 + 跨 realm 一致性 + 运行期翻转
  function getWebdriverSpoofProbe() {
    return safe("webdriverSpoofProbe", function () {
      var iframeResult = null;
      var iframe = document.createElement("iframe");
      iframe.style.display = "none";
      document.body.appendChild(iframe);
      iframeResult = {
        frameWebdriver: iframe.contentWindow.navigator.webdriver,
        sameAsMain: iframe.contentWindow.navigator.webdriver === navigator.webdriver
      };
      iframe.remove();
      return {
        value: navigator.webdriver,
        descriptorOnPrototype: !!Object.getOwnPropertyDescriptor(Navigator.prototype, "webdriver"),
        iframe: iframeResult,
        samples: antiFp.webdriverSamples.slice(-10),
        flipDetected: antiFp.webdriverFlip,
        sampleCount: antiFp.webdriverSamples.length
      };
    }, null);
  }

  function probeDebugPort(port) {
    var urls = [
      "http://127.0.0.1:" + port + "/json/version",
      "http://localhost:" + port + "/json/version"
    ];
    var timeoutMs = 900;
    var attempts = urls.map(function (url) {
      return new Promise(function (resolve) {
        var settled = false;
        var timer = setTimeout(function () {
          if (!settled) { settled = true; resolve({ url: url, status: "timeout" }); }
        }, timeoutMs);
        fetch(url, { mode: "no-cors", cache: "no-store" }).then(function () {
          if (!settled) { settled = true; clearTimeout(timer); resolve({ url: url, status: "reachable" }); }
        }).catch(function (error) {
          if (!settled) {
            settled = true;
            clearTimeout(timer);
            resolve({ url: url, status: "blocked-or-closed", error: error && error.name ? error.name : "fetch-error" });
          }
        });
      });
    });
    return Promise.all(attempts).then(function (results) {
      return { port: port, reachable: results.some(function (r) { return r.status === "reachable"; }), results: results };
    });
  }

  function runDebugPortProbe() {
    return Promise.all([9222, 9223].map(probeDebugPort)).then(function (ports) {
      return {
        checkedPorts: ports,
        reachablePorts: ports.filter(function (p) { return p.reachable; }).map(function (p) { return p.port; }),
        note: "Only common local debug ports are checked. Browser policy / file origin / private-network rules can affect this signal."
      };
    }).catch(function (error) {
      return { checkedPorts: [], reachablePorts: [], error: error && error.message ? error.message : String(error) };
    });
  }

  /* ================================================================
   * 8. 全局行为统计
   * ================================================================ */
  function getBehaviorSnapshot() {
    var clicks = events.filter(function (e) { return e.type === "click"; });
    var keydowns = events.filter(function (e) { return e.type === "keydown"; });
    var pointerMoves = events.filter(function (e) { return e.type === "pointermove"; });

    var clickIntervals = [];
    for (var i = 1; i < clicks.length; i += 1) { clickIntervals.push(clicks[i].t - clicks[i - 1].t); }
    var keyIntervals = [];
    for (var j = 1; j < keydowns.length; j += 1) { keyIntervals.push(keydowns[j].t - keydowns[j - 1].t); }

    var trustedClicks = clicks.filter(function (c) { return c.trusted; });
    var centerClicks = trustedClicks.filter(function (c) {
      return c.centerDistanceRatio !== undefined && c.centerDistanceRatio !== null && c.centerDistanceRatio < 0.08;
    }).length;
    var teleportClicks = trustedClicks.filter(function (c) {
      return !lastEventBefore(c.probe, ["pointermove", "mousemove", "mouseover", "pointerover"], c.t, 1500);
    }).length;

    var coordSeen = {};
    var repeatedCoords = 0;
    trustedClicks.forEach(function (c) {
      if (c.x === null || c.x === undefined) { return; }
      var key = c.x + "," + c.y;
      coordSeen[key] = (coordSeen[key] || 0) + 1;
      if (coordSeen[key] === 3) { repeatedCoords += 1; }
    });

    var coalescedZero = pointerMoves.filter(function (m) { return m.coalesced === 0; }).length;

    return {
      elapsedMs: Math.round(performance.now() - startedAt),
      firstInteractionAtMs: behavior.firstInteractionAt,
      moves: behavior.moves,
      clicks: behavior.clicks,
      wheels: behavior.wheels,
      scrolls: behavior.scrolls,
      keydowns: behavior.keydowns,
      paste: behavior.paste,
      visibilityChanges: behavior.visibilityChanges,
      eventCount: events.length,
      untrustedEvents: behavior.untrustedEvents,
      untrustedByType: behavior.untrustedByType,
      clickIntervalStddev: Math.round(stddev(clickIntervals)),
      keyIntervalStddev: Math.round(stddev(keyIntervals)),
      trustedClicks: trustedClicks.length,
      centerClickRatio: trustedClicks.length ? Number((centerClicks / trustedClicks.length).toFixed(2)) : 0,
      teleportClicks: teleportClicks,
      repeatedCoordinateClicks: repeatedCoords,
      coalescedZeroMoves: coalescedZero,
      pointerMoveCount: pointerMoves.length,
      silentValueMutations: silentValueMutations.slice(-10),
      resizes: behavior.resizes.slice(-10)
    };
  }

  /* ================================================================
   * 9. 评分
   * ================================================================ */
  function addFinding(findings, category, title, detail, points, severity) {
    findings.push({ category: category, title: title, detail: detail, points: points, severity: severity || "info" });
  }

  function scoreReport(report) {
    var findings = [];
    var nav = report.navigator;
    var env = report.environment;
    var webgl = report.graphics.webgl;
    var b = report.behavior;
    var verdicts = report.verdicts;

    /* ---- A. AgentRuntime 专属痕迹（石锤级） ---- */
    if (report.traces.length) {
      var kinds = {};
      report.traces.forEach(function (t) { kinds[t.kind.split(":")[0]] = (kinds[t.kind.split(":")[0]] || 0) + 1; });
      var kindText = Object.keys(kinds).map(function (k) { return k + "×" + kinds[k]; }).join(", ");
      addFinding(findings, "AgentRuntime痕迹",
        "捕获 AgentRuntime 注入痕迹 " + report.traces.length + " 条",
        "命中特征: " + kindText + "。data-hi / playwright-highlight-container / x5-overlay 均为该 Agent 独有标记。",
        45, "danger");
    }

    /* ---- B. 自动化框架直接信号 ---- */
    if (nav.webdriver === true) {
      addFinding(findings, "自动化框架", "navigator.webdriver 为 true", "浏览器明确暴露 WebDriver 自动化控制状态。", 35, "danger");
    }
    if (nav.webdriverDescriptor && !nav.webdriverDescriptor.onPrototype) {
      addFinding(findings, "自动化框架", "webdriver 描述符不在 Navigator.prototype 上",
        "stealth patch 常以 own property 覆盖，描述符位置异常。", 10, "warn");
    }
    if (/HeadlessChrome/i.test(nav.userAgent)) {
      addFinding(findings, "自动化框架", "User-Agent 包含 HeadlessChrome", "headless 自动化环境的直接信号。", 30, "danger");
    }
    if (report.automationGlobals.length) {
      addFinding(findings, "自动化框架", "发现自动化框架全局变量", report.automationGlobals.join(", "), 25, "danger");
    }

    /* ---- C. 事件保真度（靶场 verdict 汇总） ---- */
    var dangerVerdicts = [];
    var warnVerdicts = [];
    Object.keys(verdicts).forEach(function (probe) {
      verdicts[probe].forEach(function (v) {
        var text = "[" + probe + "] " + v.text;
        if (v.level === "danger") { dangerVerdicts.push(text); }
        else if (v.level === "warn") { warnVerdicts.push(text); }
      });
    });
    if (dangerVerdicts.length) {
      addFinding(findings, "事件保真度", "发现 " + dangerVerdicts.length + " 条 JS 合成/静默改写事件",
        dangerVerdicts.slice(0, 6).join("；"), 25, "danger");
    }
    if (warnVerdicts.length) {
      addFinding(findings, "事件保真度", "发现 " + warnVerdicts.length + " 条 CDP 合成事件特征",
        warnVerdicts.slice(0, 8).join("；"), Math.min(20, 6 + warnVerdicts.length * 2), "warn");
    }

    /* ---- D. 行为统计 ---- */
    if (b.elapsedMs > 3000 && b.clicks >= 2 && b.moves === 0) {
      addFinding(findings, "行为统计", "多次点击但没有鼠标移动", "桌面真人操作一般会在点击前产生 pointer/mouse 轨迹。", 12, "warn");
    }
    if (b.teleportClicks >= 2) {
      addFinding(findings, "行为统计", "多次点击前缺少指针轨迹",
        "CDP/自动化直接派发底层点击，页面只能看到点击、没有自然接近过程。命中 " + b.teleportClicks + " 次。", 10, "warn");
    }
    if (b.trustedClicks >= 3 && b.centerClickRatio >= 0.75) {
      addFinding(findings, "行为统计", "点击落点高度集中在元素中心",
        "自动化工具常默认点击元素几何中心，真人点击落点噪声更大。", 8, "warn");
    }
    if (b.repeatedCoordinateClicks > 0) {
      addFinding(findings, "行为统计", "多次点击完全相同坐标", "重复坐标命中常见于脚本化动作或固定录制回放。", 6, "warn");
    }
    if (b.pointerMoveCount >= 10 && b.coalescedZeroMoves / b.pointerMoveCount > 0.9) {
      addFinding(findings, "行为统计", "pointermove 全部无 coalesced events",
        "真实鼠标在 rAF 对齐下通常携带合并样本，CDP 单步移动 getCoalescedEvents() 恒为空。", 8, "warn");
    }
    if (b.clicks >= 4 && b.clickIntervalStddev > 0 && b.clickIntervalStddev < 80) {
      addFinding(findings, "行为统计", "点击节奏过于稳定", "多次点击间隔波动很低，可能是脚本节拍。", 7, "warn");
    }
    if (b.keydowns >= 8 && b.keyIntervalStddev > 0 && b.keyIntervalStddev < 35) {
      addFinding(findings, "行为统计", "输入节奏过于稳定", "连续输入间隔波动很低，可能是脚本注入或自动输入。", 8, "warn");
    }
    if (b.firstInteractionAtMs !== null && b.firstInteractionAtMs < 250) {
      addFinding(findings, "行为统计", "首个交互发生过快", "页面加载后极短时间内开始操作，弱风险信号。", 4, "info");
    }

    /* ---- E. CDP / Inspector ---- */
    var cdp = report.cdpSerializationProbe;
    if (cdp.consoleGetterHit || cdp.errorStackGetterHit || cdp.toJsonHit) {
      addFinding(findings, "CDP/Inspector", "console 序列化探针被触发",
        "getter×" + cdp.consoleGetterHit + " stackGetter×" + cdp.errorStackGetterHit + " toJSON×" + cdp.toJsonHit +
        "。说明存在读取 console 对象预览的调试器/CDP 客户端。", 8, "warn");
    }
    if (report.debuggerTimingProbe && report.debuggerTimingProbe.maxMs > 120) {
      addFinding(findings, "CDP/Inspector", "debugger 语句出现明显暂停",
        "max " + report.debuggerTimingProbe.maxMs + "ms，可能存在已启用 Debugger domain 的控制端。", 12, "warn");
    }
    if (report.errorStackProbe && report.errorStackProbe.automationHints.length) {
      addFinding(findings, "CDP/Inspector", "Error.stack 出现自动化相关帧",
        report.errorStackProbe.automationHints.join(" | "), 15, "warn");
    }
    if (report.debugPortProbe && report.debugPortProbe.reachablePorts.length) {
      addFinding(findings, "CDP/Inspector", "发现常见本地 debug 端口可达",
        "可达端口: " + report.debugPortProbe.reachablePorts.join(", ") + "，可能开启了 remote debugging。", 18, "warn");
    }

    /* ---- F. 运行时一致性 ---- */
    if (/Chrome/i.test(nav.userAgent) && !env.chromeObject.present) {
      addFinding(findings, "一致性", "Chrome UA 但缺少 window.chrome", "UA 与 Chrome 专属对象不一致。", 8, "warn");
    }
    if (/Chrome/i.test(nav.userAgent) && env.chromeObject.present && !env.chromeObject.hasRuntime) {
      addFinding(findings, "一致性", "window.chrome 缺少 runtime", "真实 Chrome 页面环境通常暴露 chrome.runtime。", 5, "info");
    }
    if (nav.userAgentData && nav.userAgentData.platform && nav.platform) {
      var chp = nav.userAgentData.platform.toLowerCase();
      var np = nav.platform.toLowerCase();
      if ((chp.indexOf("windows") !== -1 && np.indexOf("win") === -1) ||
          (chp.indexOf("mac") !== -1 && np.indexOf("mac") === -1)) {
        addFinding(findings, "一致性", "UA-CH platform 与 navigator.platform 不一致", "平台相关信号组合不自洽。", 10, "warn");
      }
    }
    if (report.highEntropyUserAgentData && report.highEntropyUserAgentData.fullVersionList) {
      var uaMatch = nav.userAgent.match(/Chrome\/([\d.]+)/);
      var fv = report.highEntropyUserAgentData.fullVersionList;
      var chromeFv = fv.filter(function (b) { return /chrom/i.test(b.brand); })[0];
      if (uaMatch && chromeFv && uaMatch[1] !== chromeFv.version) {
        addFinding(findings, "一致性", "UA 版本号与 UA-CH fullVersionList 不一致",
          "UA: " + uaMatch[1] + " vs UA-CH: " + chromeFv.version, 10, "warn");
      }
    }
    if (report.permissionsConsistency && report.permissionsConsistency.notificationMismatch) {
      addFinding(findings, "一致性", "permissions.query(notifications) 与 Notification.permission 不一致",
        "query=" + JSON.stringify(report.permissionsConsistency.results) +
        "，Notification.permission=" + report.permissionsConsistency.notificationPermission +
        "（经典 headless 检测项，同时用于回归内核权限对抗改动）。", 12, "warn");
    }
    if (report.iframeConsistency) {
      var ic = report.iframeConsistency;
      if (!ic.webdriverSame || !ic.chromeSamePresence) {
        addFinding(findings, "一致性", "主页面与 iframe clean realm 不一致",
          "可能存在 JS API patch 或自动化注入未覆盖所有执行上下文。", 12, "warn");
      }
      if (ic.permissionsQuerySameSource === false || ic.clickSameSource === false || ic.toStringSameSource === false) {
        addFinding(findings, "一致性", "原生函数源码跨 realm 不一致",
          "permissionsQuery=" + ic.permissionsQuerySameSource + " click=" + ic.clickSameSource +
          " toString=" + ic.toStringSameSource + "，原生对象可能被改写或代理。", 10, "warn");
      }
      if (ic.webdriverDescriptor === "own") {
        addFinding(findings, "一致性", "webdriver 是 navigator 自有属性",
          "正常实现位于 Navigator.prototype，own property 常见于 patch。", 8, "warn");
      }
    }
    report.nativeIntegrity.forEach(function (item) {
      if (item.nativeLike === false) {
        addFinding(findings, "一致性", item.name + " 不像原生函数",
          "Function.prototype.toString 未呈现 [native code]。", 8, "warn");
      }
    });

    /* ---- G. 环境指纹 ---- */
    if (!nav.languages || nav.languages.length === 0) {
      addFinding(findings, "环境指纹", "navigator.languages 为空", "真实桌面浏览器通常暴露至少一个语言。", 8, "warn");
    }
    if (nav.pluginsLength === 0 && /Chrome/i.test(nav.userAgent)) {
      addFinding(findings, "环境指纹", "plugins 为空", "完全为空可作为弱风险信号。", 5, "warn");
    }
    if (env.viewport.outerWidth === 0 || env.viewport.outerHeight === 0) {
      addFinding(findings, "环境指纹", "outerWidth/outerHeight 异常", "窗口外框尺寸为 0 常见于 headless 或嵌入环境。", 12, "warn");
    }
    if (env.viewport.innerWidth > env.screen.width || env.viewport.innerHeight > env.screen.height) {
      addFinding(findings, "环境指纹", "viewport 大于物理屏幕", "视口尺寸超过屏幕尺寸，可能是虚拟/仿真环境。", 8, "warn");
    }
    if (env.screen.colorDepth && env.screen.colorDepth < 24) {
      addFinding(findings, "环境指纹", "colorDepth 异常 (" + env.screen.colorDepth + ")", "现代桌面设备通常为 24/30。", 5, "info");
    }
    if (webgl && webgl.supported && /swiftshader|llvmpipe|mesa|software|angle \(google/i.test(String(webgl.renderer))) {
      addFinding(findings, "环境指纹", "WebGL renderer 呈现软件/虚拟化特征", String(webgl.renderer), 9, "warn");
    }
    if (report.mediaDevices && report.mediaDevices.total === 0) {
      addFinding(findings, "环境指纹", "无任何媒体设备", "enumerateDevices 返回 0，headless/虚机常见。", 4, "info");
    }
    if (report.speechVoices && report.speechVoices.supported && report.speechVoices.count === 0) {
      addFinding(findings, "环境指纹", "speechSynthesis 语音列表为空", "真实桌面系统通常有 TTS 语音。", 4, "info");
    }
    if (env.mediaQueries && env.mediaQueries.pointerCoarse && nav.maxTouchPoints === 0) {
      addFinding(findings, "环境指纹", "pointer:coarse 但 maxTouchPoints=0", "媒体查询与触摸能力不一致。", 6, "warn");
    }

    /* ---- H. 内核对抗回归（commit f98b861a webdriver 伪装 / 9eef07f0 inspector 抑制） ---- */
    function hasAnyCdpEvidence() {
      return cdp.consoleGetterHit > 0 || cdp.errorStackGetterHit > 0 || cdp.toJsonHit > 0 ||
        (report.debuggerTimingProbe && report.debuggerTimingProbe.maxMs > 120) ||
        (report.debugPortProbe && report.debugPortProbe.reachablePorts.length > 0) ||
        report.traces.length > 0 ||
        (report.exceptionSerializationProbe && report.exceptionSerializationProbe.exceptionGetterHit > 0);
    }

    var wsp = report.webdriverSpoofProbe;
    if (wsp) {
      if (wsp.value === true) {
        addFinding(findings, "内核对抗回归", "webdriver 伪装未生效",
          "navigator.webdriver=true：--enable-automation 仍在强制置位。f98b861a 的 spoof 未命中（FingerprintHooks 开关未开），或命中了被刻意保留的 DevTools override 路径（probe::ApplyAutomationOverride）。",
          0, "info");
      } else if (wsp.value === false && hasAnyCdpEvidence()) {
        addFinding(findings, "内核对抗回归", "webdriver 已伪装但 CDP/AgentRuntime 痕迹仍可检出",
          "webdriver=false 的同时存在 CDP attach 或 AgentRuntime 信号——单点伪装无法通过组合检测，前端风控按组合信号判定。",
          0, "warn");
      } else if (wsp.value === false && wsp.sampleCount > 4 && !hasAnyCdpEvidence()) {
        addFinding(findings, "内核对抗回归", "webdriver 伪装稳定且未见 CDP 残留信号",
          "webdriver 恒为 false，console/debugger/端口/痕迹探针均无命中。", 0, "ok");
      }
      if (wsp.flipDetected) {
        addFinding(findings, "内核对抗回归", "navigator.webdriver 运行期发生翻转",
          "spoof 取值在页面生命周期内发生变化，开关不稳定本身即为强异常信号。", 15, "danger");
      }
      if (wsp.iframe && wsp.iframe.sameAsMain === false) {
        addFinding(findings, "内核对抗回归", "webdriver 跨 realm 不一致",
          "主页面与 iframe clean realm 取值不同，伪装未覆盖全部执行上下文。", 12, "warn");
      }
    }

    var esp = report.exceptionSerializationProbe;
    if (esp && (esp.exceptionGetterHit > 0 || esp.exceptionToStringHit > 0)) {
      addFinding(findings, "内核对抗回归", "异常通道仍在触发 inspector 序列化",
        "uncaught exception / unhandled rejection 的 preview 序列化触发 getter " +
        (esp.exceptionGetterHit + esp.exceptionToStringHit) +
        " 次。9eef07f0 的 Runtime inspector 抑制若只覆盖 console 路径，Runtime.exceptionThrown 仍可作旁路检测。",
        10, "warn");
    }

    var wp = report.workerProbe;
    if (wp && wp.supported && !wp.error && !wp.timeout) {
      if (wp.consoleGetterHit > 0 || wp.errorStackGetterHit > 0) {
        addFinding(findings, "内核对抗回归", "Worker isolate 内 console 序列化探针被触发",
          "Worker 内 getter 命中 " + (wp.consoleGetterHit + wp.errorStackGetterHit) +
          " 次。9eef07f0 声称覆盖每个 Worker isolate，此处命中说明抑制在 Worker 上未生效。",
          10, "warn");
      }
      if (wp.debuggerMaxMs > 120) {
        addFinding(findings, "内核对抗回归", "Worker 内 debugger 语句出现明显暂停",
          "Worker debugger 最大耗时 " + wp.debuggerMaxMs + "ms，存在已启用 Debugger 的控制端。", 10, "warn");
      }
      if (wp.consoleGetterHit === 0 && wp.errorStackGetterHit === 0 && wp.debuggerMaxMs <= 120) {
        addFinding(findings, "内核对抗回归", "Worker isolate 探针无命中",
          "Worker 内 console getter / debugger 时序均无异常，inspector 抑制（若开启）在 Worker 上生效。", 0, "ok");
      }
      if (wp.webdriver !== "property-absent" && wp.webdriver !== navigator.webdriver) {
        addFinding(findings, "内核对抗回归", "Worker 与主页面 webdriver 取值不一致",
          "Worker=" + wp.webdriver + " / Main=" + navigator.webdriver + "，跨 isolate 伪装不一致。", 8, "warn");
      }
    } else if (wp && wp.timeout) {
      addFinding(findings, "内核对抗回归", "Worker 探针超时",
        "Worker 内探针未在 4s 内返回，可能被 debugger 暂停或环境异常。", 4, "info");
    }

    /* ---- 兜底 ---- */
    if (!findings.length) {
      addFinding(findings, "结论", "未发现明显自动化信号",
        "当前结果更接近普通人工浏览，但仍需结合服务端网络和业务数据综合判断。", 0, "ok");
    }

    var score = findings.reduce(function (sum, f) { return sum + f.points; }, 0);
    score = Math.max(0, Math.min(100, score));
    return { score: score, classification: classify(score), findings: findings };
  }

  function classify(score) {
    if (score >= 71) { return { label: "high confidence automation", level: "danger" }; }
    if (score >= 46) { return { label: "likely automation", level: "danger" }; }
    if (score >= 21) { return { label: "suspicious", level: "warn" }; }
    return { label: "human-like", level: "ok" };
  }

  /* ================================================================
   * 10. 渲染
   * ================================================================ */
  var CATEGORY_ORDER = ["AgentRuntime痕迹", "自动化框架", "事件保真度", "行为统计", "CDP/Inspector", "一致性", "环境指纹", "内核对抗回归", "结论"];

  function buildSummary(report) {
    return CATEGORY_ORDER.map(function (cat) {
      var items = report.score.findings.filter(function (f) { return f.category === cat && f.points > 0; });
      return { label: cat, value: items.length, level: items.length ? (items.some(function (f) { return f.severity === "danger"; }) ? "danger" : "warn") : "ok" };
    }).filter(function (m) { return m.label !== "结论"; });
  }

  function renderTrace() {
    var el = document.getElementById("traceLog");
    if (!el) { return; }
    if (!traceLog.length) {
      el.innerHTML = '<p class="empty">暂无异动记录。让 Agent 执行 get_state / click_element 后观察此处。</p>';
      return;
    }
    el.innerHTML = traceLog.slice(-40).reverse().map(function (t) {
      return '<div class="trace-row"><span class="trace-time">' + t.t + 'ms</span>' +
        '<span class="trace-kind">' + escapeHtml(t.kind) + '</span>' +
        '<span class="trace-detail">' + escapeHtml(t.detail) + '</span></div>';
    }).join("");
  }

  function renderTimeline() {
    var el = document.getElementById("timeline");
    if (!el) { return; }
    var recent = events.filter(function (e) {
      return e.type !== "pointermove" && e.type !== "mousemove";
    }).slice(-80).reverse();
    if (!recent.length) {
      el.innerHTML = '<p class="empty">暂无事件</p>';
      return;
    }
    el.innerHTML = recent.map(function (e) {
      var extras = [];
      if (e.x !== undefined && e.x !== null) { extras.push("(" + e.x + "," + e.y + ")"); }
      if (e.key) { extras.push("key=" + e.key); }
      if (e.inputType) { extras.push(e.inputType); }
      if (e.detail !== undefined && e.detail !== null && e.type !== "wheel") { extras.push("detail=" + e.detail); }
      if (e.deltaY !== undefined) { extras.push("deltaY=" + e.deltaY); }
      if (e.centerDistancePx !== undefined && e.centerDistancePx !== null) { extras.push("centerΔ=" + e.centerDistancePx + "px"); }
      return '<div class="tl-row">' +
        '<span class="tl-time">' + e.t + 'ms</span>' +
        '<span class="tl-type">' + escapeHtml(e.type) + '</span>' +
        '<span class="mini-tag ' + (e.trusted ? "trusted" : "untrusted") + '">' + (e.trusted ? "trusted" : "untrusted") + '</span>' +
        '<span class="tl-target">' + escapeHtml(e.target) + '</span>' +
        '<span class="tl-extra">' + escapeHtml(extras.join(" ")) + '</span></div>';
    }).join("");
  }

  function renderVerdicts(verdicts) {
    Object.keys(verdicts).forEach(function (probe) {
      var el = document.querySelector('[data-verdict="' + probe + '"]');
      if (!el) { return; }
      var list = verdicts[probe];
      if (!list.length) {
        el.className = "verdict";
        el.textContent = "已采样，暂无异常特征";
        return;
      }
      var worst = list.some(function (v) { return v.level === "danger"; }) ? "danger" :
        (list.some(function (v) { return v.level === "warn"; }) ? "warn" : "info");
      el.className = "verdict " + worst;
      el.innerHTML = list.map(function (v) {
        return '<div class="verdict-line ' + v.level + '">' + escapeHtml(v.text) + '</div>';
      }).join("");
    });
  }

  function render(report) {
    var scoreEl = document.getElementById("riskScore");
    var classificationEl = document.getElementById("classification");
    var findingsEl = document.getElementById("findings");
    var rawEl = document.getElementById("rawReport");
    var summaryGrid = document.getElementById("summaryGrid");

    scoreEl.textContent = report.score.score;
    classificationEl.textContent = report.score.classification.label;
    classificationEl.className = "classification " + report.score.classification.level;

    summaryGrid.innerHTML = buildSummary(report).map(function (metric) {
      return '<article class="metric ' + metric.level + '"><span>' + escapeHtml(metric.label) +
        '</span><strong>' + escapeHtml(metric.value) + '</strong></article>';
    }).join("");

    findingsEl.innerHTML = report.score.findings.map(function (f) {
      return [
        '<article class="finding ', f.severity, '">',
        '<span class="tag">', escapeHtml(f.category), '</span>',
        '<div><strong>', escapeHtml(f.title), '</strong><p>', escapeHtml(f.detail), '</p></div>',
        '<span class="points">+', f.points, '</span>',
        '</article>'
      ].join("");
    }).join("");

    rawEl.textContent = JSON.stringify(report, null, 2);
    renderTrace();
    renderTimeline();
    renderVerdicts(report.verdicts);
    document.getElementById("statusText").textContent =
      "检测完成于 " + new Date().toLocaleTimeString() + "，数据仅保存在当前浏览器。";
  }

  /* ================================================================
   * 11. 主流程
   * ================================================================ */
  function runDetection() {
    document.getElementById("statusText").textContent = "正在采集信号...";
    return Promise.all([
      getHighEntropyValues(),
      getAudioHash(),
      runDebugPortProbe(),
      getPermissionsConsistency(),
      getMediaDevicesCount(),
      runWorkerProbe()
    ]).then(function (values) {
      var report = {
        generatedAt: new Date().toISOString(),
        location: location.href,
        navigator: getNavigatorData(),
        highEntropyUserAgentData: values[0],
        environment: getEnvironmentData(),
        automationGlobals: getAutomationGlobals(),
        cdpSerializationProbe: runCdpSerializationProbe(),
        debuggerTimingProbe: runDebuggerTimingProbe(),
        errorStackProbe: getErrorStackProbe(),
        debugPortProbe: values[2],
        permissionsConsistency: values[3],
        mediaDevices: values[4],
        speechVoices: getSpeechVoices(),
        iframeConsistency: getIframeConsistency(),
        nativeIntegrity: getNativeIntegrity(),
        webdriverSpoofProbe: getWebdriverSpoofProbe(),
        exceptionSerializationProbe: runExceptionSerializationProbe(),
        workerProbe: values[5],
        graphics: {
          canvasHash: getCanvasHash(),
          webgl: getWebglInfo(),
          audioHash: values[1]
        },
        traces: traceLog.slice(),
        behavior: getBehaviorSnapshot(),
        verdicts: computeVerdicts()
      };
      report.score = scoreReport(report);
      lastReport = report;
      render(report);
      return report;
    });
  }

  var detectTimer = null;
  function scheduleDetection() {
    if (detectTimer) { return; }
    detectTimer = setTimeout(function () {
      detectTimer = null;
      runDetection();
    }, 400);
  }

  function resetBehavior() {
    startedAt = performance.now();
    events = [];
    traceLog = [];
    silentValueMutations = [];
    lastKnownValues = {};
    behavior = {
      moves: 0, clicks: 0, wheels: 0, scrolls: 0, keydowns: 0,
      paste: 0, visibilityChanges: 0, firstInteractionAt: null,
      untrustedEvents: 0, untrustedByType: {}, resizes: []
    };
    cdpProbe.consoleGetterHit = 0;
    cdpProbe.errorStackGetterHit = 0;
    cdpProbe.toJsonHit = 0;
    antiFp.webdriverSamples = [];
    antiFp.webdriverFlip = false;
    antiFp.exceptionGetterHit = 0;
    antiFp.exceptionToStringHit = 0;
    runDetection();
  }

  function exportReport() {
    if (!lastReport) { return; }
    var blob = new Blob([JSON.stringify(lastReport, null, 2)], { type: "application/json" });
    var url = URL.createObjectURL(blob);
    var link = document.createElement("a");
    link.href = url;
    link.download = "agent-detection-report.json";
    document.body.appendChild(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
  }

  /* ================================================================
   * 12. 启动
   * ================================================================ */
  startTraceObserver();
  startEventCapture();
  sweepExistingMarkers();

  // 交互后触发即时重检（事件捕获是 capture 阶段，业务渲染走 schedule 防抖）
  ["click", "keydown", "input", "change", "drop", "wheel"].forEach(function (type) {
    window.addEventListener(type, scheduleDetection, { passive: true });
  });

  if (window.speechSynthesis) {
    window.speechSynthesis.addEventListener("voiceschanged", scheduleDetection);
  }

  document.getElementById("runBtn").addEventListener("click", runDetection);
  document.getElementById("exportBtn").addEventListener("click", exportReport);
  document.getElementById("resetBehaviorBtn").addEventListener("click", resetBehavior);

  runDetection();
  setInterval(runDetection, 5000);
}());
