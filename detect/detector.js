(function () {
  "use strict";

  var behavior = {
    startedAt: performance.now(),
    moves: 0,
    clicks: 0,
    wheels: 0,
    scrolls: 0,
    keydowns: 0,
    paste: 0,
    pointerSamples: [],
    clickTimes: [],
    keyIntervals: [],
    lastKeyAt: 0,
    firstInteractionAt: null,
    visibilityChanges: 0
  };

  var lastReport = null;
  var cdpProbe = {
    consoleGetterHit: 0,
    errorStackGetterHit: 0,
    lastRunAt: 0,
    debuggerSamples: [],
    localhostPorts: []
  };

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

  function markInteraction() {
    if (behavior.firstInteractionAt === null) {
      behavior.firstInteractionAt = Math.round(performance.now() - behavior.startedAt);
    }
  }

  function pushLimited(list, item, limit) {
    list.push(item);
    if (list.length > limit) {
      list.shift();
    }
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
      if (!gl) {
        return { supported: false };
      }
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
      if (!AudioCtx) {
        return Promise.resolve(null);
      }
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
      }).catch(function () {
        return null;
      });
    }, Promise.resolve(null));
  }

  function getNativeIntegrity() {
    return safe("nativeIntegrity", function () {
      var checks = [];
      function add(name, value) {
        var source = Function.prototype.toString.call(value);
        checks.push({
          name: name,
          nativeLike: source.indexOf("[native code]") !== -1,
          hash: hashString(source)
        });
      }
      add("permissions.query", navigator.permissions && navigator.permissions.query);
      add("canvas.toDataURL", HTMLCanvasElement.prototype.toDataURL);
      add("webgl.getParameter", window.WebGLRenderingContext && WebGLRenderingContext.prototype.getParameter);
      return checks;
    }, []);
  }

  function getIframeConsistency() {
    return safe("iframeConsistency", function () {
      var iframe = document.createElement("iframe");
      iframe.setAttribute("title", "clean realm probe");
      iframe.style.display = "none";
      document.body.appendChild(iframe);
      var frameWindow = iframe.contentWindow;
      var result = {
        webdriverSame: navigator.webdriver === frameWindow.navigator.webdriver,
        languagesSame: JSON.stringify(navigator.languages) === JSON.stringify(frameWindow.navigator.languages),
        chromeSamePresence: Boolean(window.chrome) === Boolean(frameWindow.chrome),
        permissionsQuerySameSource: null,
        webdriverDescriptor: Object.getOwnPropertyDescriptor(Navigator.prototype, "webdriver"),
        frameWebdriverDescriptor: Object.getOwnPropertyDescriptor(frameWindow.Navigator.prototype, "webdriver")
      };
      if (navigator.permissions && frameWindow.navigator.permissions) {
        result.permissionsQuerySameSource =
          Function.prototype.toString.call(navigator.permissions.query) ===
          frameWindow.Function.prototype.toString.call(frameWindow.navigator.permissions.query);
      }
      iframe.remove();
      return result;
    }, null);
  }

  function getAutomationGlobals() {
    var names = [
      "__webdriver_evaluate",
      "__selenium_evaluate",
      "__webdriver_script_function",
      "__webdriver_script_func",
      "__webdriver_script_fn",
      "__fxdriver_evaluate",
      "__driver_unwrapped",
      "__webdriver_unwrapped",
      "__selenium_unwrapped",
      "__fxdriver_unwrapped",
      "_Selenium_IDE_Recorder",
      "_selenium",
      "callSelenium",
      "_phantom",
      "phantom",
      "domAutomation",
      "domAutomationController",
      "__playwright",
      "__puppeteer_utility_world__"
    ];
    return names.filter(function (name) {
      return name in window || name in document;
    });
  }

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
        lastRunAt: cdpProbe.lastRunAt,
        note: "Getter hits can happen when a CDP Runtime client requests console object previews."
      };
    }, {
      consoleGetterHit: cdpProbe.consoleGetterHit,
      errorStackGetterHit: cdpProbe.errorStackGetterHit,
      lastRunAt: cdpProbe.lastRunAt,
      note: "probe failed"
    });
  }

  function runDebuggerTimingProbe() {
    return safe("debuggerTimingProbe", function () {
      var samples = [];
      for (var i = 0; i < 3; i += 1) {
        var before = performance.now();
        // This intentionally measures whether an attached inspector pauses on debugger statements.
        debugger;
        samples.push(Number((performance.now() - before).toFixed(3)));
      }
      cdpProbe.debuggerSamples = samples;
      return {
        samplesMs: samples,
        maxMs: Math.max.apply(Math, samples),
        avgMs: Number((samples.reduce(function (sum, value) { return sum + value; }, 0) / samples.length).toFixed(3))
      };
    }, {
      samplesMs: [],
      maxMs: 0,
      avgMs: 0,
      error: "debugger timing probe failed"
    });
  }

  function getErrorStackProbe() {
    return safe("errorStackProbe", function () {
      var stack = new Error("automation-stack-probe").stack || "";
      var lines = stack.split("\n").map(function (line) { return line.trim(); }).filter(Boolean);
      var automationHints = lines.filter(function (line) {
        return /puppeteer|playwright|selenium|webdriver|__puppeteer|__playwright|evaluate|ExecutionContext|Runtime\.evaluate/i.test(line);
      });
      return {
        lineCount: lines.length,
        firstLine: lines[0] || "",
        formatHash: hashString(lines.slice(0, 6).join("\n")),
        automationHints: automationHints.slice(0, 8),
        stackTraceLimit: Error.stackTraceLimit
      };
    }, {
      lineCount: 0,
      firstLine: "",
      formatHash: null,
      automationHints: [],
      error: "stack probe failed"
    });
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
          if (!settled) {
            settled = true;
            resolve({ url: url, status: "timeout" });
          }
        }, timeoutMs);

        fetch(url, {
          mode: "no-cors",
          cache: "no-store"
        }).then(function () {
          if (!settled) {
            settled = true;
            clearTimeout(timer);
            resolve({ url: url, status: "reachable" });
          }
        }).catch(function (error) {
          if (!settled) {
            settled = true;
            clearTimeout(timer);
            resolve({
              url: url,
              status: "blocked-or-closed",
              error: error && error.name ? error.name : "fetch-error"
            });
          }
        });
      });
    });

    return Promise.all(attempts).then(function (results) {
      return {
        port: port,
        reachable: results.some(function (item) { return item.status === "reachable"; }),
        results: results
      };
    });
  }

  function runDebugPortProbe() {
    return Promise.all([9222, 9223].map(probeDebugPort)).then(function (ports) {
      cdpProbe.localhostPorts = ports;
      return {
        checkedPorts: ports,
        reachablePorts: ports.filter(function (item) { return item.reachable; }).map(function (item) { return item.port; }),
        note: "Only common local debug ports are checked. Browser policy, file origin, CORS, or private-network rules can affect this signal."
      };
    }).catch(function (error) {
      return {
        checkedPorts: [],
        reachablePorts: [],
        error: error && error.message ? error.message : String(error)
      };
    });
  }

  function getNavigatorData() {
    return {
      userAgent: navigator.userAgent,
      platform: navigator.platform,
      vendor: navigator.vendor,
      webdriver: navigator.webdriver,
      languages: navigator.languages ? Array.prototype.slice.call(navigator.languages) : [],
      language: navigator.language,
      hardwareConcurrency: navigator.hardwareConcurrency,
      deviceMemory: navigator.deviceMemory,
      maxTouchPoints: navigator.maxTouchPoints,
      cookieEnabled: navigator.cookieEnabled,
      doNotTrack: navigator.doNotTrack,
      pluginsLength: navigator.plugins ? navigator.plugins.length : null,
      mimeTypesLength: navigator.mimeTypes ? navigator.mimeTypes.length : null,
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
      "architecture",
      "bitness",
      "model",
      "platform",
      "platformVersion",
      "uaFullVersion",
      "fullVersionList",
      "wow64"
    ]).catch(function (error) {
      return { error: error.message };
    });
  }

  function getEnvironmentData() {
    return {
      screen: {
        width: screen.width,
        height: screen.height,
        availWidth: screen.availWidth,
        availHeight: screen.availHeight,
        colorDepth: screen.colorDepth,
        pixelDepth: screen.pixelDepth
      },
      viewport: {
        innerWidth: window.innerWidth,
        innerHeight: window.innerHeight,
        outerWidth: window.outerWidth,
        outerHeight: window.outerHeight,
        devicePixelRatio: window.devicePixelRatio
      },
      locale: {
        timezone: Intl.DateTimeFormat().resolvedOptions().timeZone,
        calendar: Intl.DateTimeFormat().resolvedOptions().calendar,
        numberingSystem: Intl.DateTimeFormat().resolvedOptions().numberingSystem
      },
      chromeObject: {
        present: Boolean(window.chrome),
        keys: window.chrome ? Object.keys(window.chrome).slice(0, 20) : []
      },
      permissions: safe("permissions", function () {
        if (!navigator.permissions || !navigator.permissions.query) {
          return { supported: false };
        }
        return { supported: true };
      })
    };
  }

  function stddev(values) {
    if (!values.length) {
      return 0;
    }
    var mean = values.reduce(function (sum, value) { return sum + value; }, 0) / values.length;
    var variance = values.reduce(function (sum, value) {
      return sum + Math.pow(value - mean, 2);
    }, 0) / values.length;
    return Math.sqrt(variance);
  }

  function getBehaviorSnapshot() {
    var clickIntervals = [];
    for (var i = 1; i < behavior.clickTimes.length; i += 1) {
      clickIntervals.push(behavior.clickTimes[i] - behavior.clickTimes[i - 1]);
    }
    var clicks = behavior.clickDetails || [];
    var centerClicks = clicks.filter(function (item) { return item.centerDistanceRatio !== null && item.centerDistanceRatio < 0.08; }).length;
    var untrustedEvents =
      (behavior.untrustedPointerMoves || 0) +
      (behavior.untrustedClicks || 0) +
      (behavior.untrustedKeys || 0);
    return {
      elapsedMs: Math.round(performance.now() - behavior.startedAt),
      firstInteractionAtMs: behavior.firstInteractionAt,
      moves: behavior.moves,
      clicks: behavior.clicks,
      wheels: behavior.wheels,
      scrolls: behavior.scrolls,
      keydowns: behavior.keydowns,
      paste: behavior.paste,
      visibilityChanges: behavior.visibilityChanges,
      pointerSampleCount: behavior.pointerSamples.length,
      clickIntervalStddev: Math.round(stddev(clickIntervals)),
      keyIntervalStddev: Math.round(stddev(behavior.keyIntervals)),
      centerClickRatio: clicks.length ? Number((centerClicks / clicks.length).toFixed(2)) : 0,
      noRecentPointerMoveClicks: behavior.noRecentPointerMoveClicks || 0,
      repeatedCoordinateClicks: countRepeatedClickCoordinates(clicks),
      straightLineApproachClicks: behavior.straightLineApproachClicks || 0,
      untrustedEvents: untrustedEvents,
      clickDetails: clicks.slice(-20),
      lastPointerSamples: behavior.pointerSamples.slice(-12)
    };
  }

  function countRepeatedClickCoordinates(clicks) {
    var seen = {};
    var repeated = 0;
    clicks.forEach(function (item) {
      var key = item.x + "," + item.y;
      seen[key] = (seen[key] || 0) + 1;
      if (seen[key] === 3) {
        repeated += 1;
      }
    });
    return repeated;
  }

  function getApproachStraightness(x, y) {
    var samples = behavior.pointerSamples.slice(-18);
    if (samples.length < 4) {
      return null;
    }
    var path = 0;
    for (var i = 1; i < samples.length; i += 1) {
      path += distance(samples[i - 1].x, samples[i - 1].y, samples[i].x, samples[i].y);
    }
    var direct = distance(samples[0].x, samples[0].y, x, y);
    if (direct < 2 || path < 2) {
      return null;
    }
    return Number((path / direct).toFixed(3));
  }

  function distance(x1, y1, x2, y2) {
    return Math.sqrt(Math.pow(x1 - x2, 2) + Math.pow(y1 - y2, 2));
  }

  function addFinding(findings, category, title, detail, points, severity) {
    findings.push({
      category: category,
      title: title,
      detail: detail,
      points: points,
      severity: severity || "info"
    });
  }

  function scoreReport(report) {
    var findings = [];
    var nav = report.navigator;
    var env = report.environment;
    var webgl = report.graphics.webgl;
    var behaviorData = report.behavior;

    if (nav.webdriver === true) {
      addFinding(findings, "强信号", "navigator.webdriver 为 true", "浏览器明确暴露 WebDriver 自动化控制状态。", 35, "danger");
    }

    if (/HeadlessChrome/i.test(nav.userAgent)) {
      addFinding(findings, "强信号", "User-Agent 包含 HeadlessChrome", "这是 headless 自动化环境的典型直接信号。", 30, "danger");
    }

    if (report.automationGlobals.length) {
      addFinding(findings, "强信号", "发现自动化框架全局变量", report.automationGlobals.join(", "), 25, "danger");
    }

    if (/Chrome/i.test(nav.userAgent) && !env.chromeObject.present) {
      addFinding(findings, "一致性", "Chrome UA 但缺少 window.chrome", "UA 与 Chrome 专属对象存在不一致。", 8, "warn");
    }

    if (nav.userAgentData && nav.userAgentData.platform && nav.platform) {
      var chPlatform = nav.userAgentData.platform.toLowerCase();
      var navPlatform = nav.platform.toLowerCase();
      if (chPlatform.indexOf("windows") !== -1 && navPlatform.indexOf("win") === -1) {
        addFinding(findings, "一致性", "UA-CH platform 与 navigator.platform 不一致", "平台相关信号组合不自洽。", 10, "warn");
      }
      if (chPlatform.indexOf("mac") !== -1 && navPlatform.indexOf("mac") === -1) {
        addFinding(findings, "一致性", "UA-CH platform 与 navigator.platform 不一致", "平台相关信号组合不自洽。", 10, "warn");
      }
    }

    if (!nav.languages || nav.languages.length === 0) {
      addFinding(findings, "环境", "navigator.languages 为空", "真实桌面浏览器通常会暴露至少一个语言。", 8, "warn");
    }

    if (nav.pluginsLength === 0 && /Chrome/i.test(nav.userAgent)) {
      addFinding(findings, "环境", "plugins 为空", "现代 Chrome 不一定依赖插件判断，但完全为空仍可作为弱风险信号。", 5, "warn");
    }

    if (env.viewport.outerWidth === 0 || env.viewport.outerHeight === 0) {
      addFinding(findings, "环境", "outerWidth/outerHeight 异常", "窗口外框尺寸为 0 常见于部分 headless 或嵌入环境。", 12, "warn");
    }

    if (webgl && webgl.supported && /swiftshader|llvmpipe|mesa|software/i.test(String(webgl.renderer))) {
      addFinding(findings, "图形", "WebGL renderer 呈现软件/虚拟化特征", String(webgl.renderer), 9, "warn");
    }

    if (report.iframeConsistency) {
      if (!report.iframeConsistency.webdriverSame || !report.iframeConsistency.chromeSamePresence) {
        addFinding(findings, "运行时", "主页面与 iframe clean realm 不一致", "可能存在 JS API patch 或自动化注入未覆盖所有执行上下文。", 12, "warn");
      }
      if (report.iframeConsistency.permissionsQuerySameSource === false) {
        addFinding(findings, "运行时", "permissions.query 源码表现不一致", "原生对象可能被改写或代理。", 10, "warn");
      }
    }

    report.nativeIntegrity.forEach(function (item) {
      if (item.nativeLike === false) {
        addFinding(findings, "运行时", item.name + " 不像原生函数", "Function.prototype.toString 未呈现 native code。", 8, "warn");
      }
    });

    if (behaviorData.elapsedMs > 3000 && behaviorData.clicks >= 2 && behaviorData.moves === 0) {
      addFinding(findings, "行为", "多次点击但没有鼠标移动", "桌面真人操作一般会在点击前产生 pointer/mouse 轨迹。", 12, "warn");
    }

    if (behaviorData.noRecentPointerMoveClicks >= 2) {
      addFinding(findings, "CDP/Puppeteer弱信号", "点击前缺少近期 pointer 轨迹", "CDP 或自动化工具可能直接派发底层点击，页面只能看到点击，没有自然接近过程。", 10, "warn");
    }

    if (behaviorData.clicks >= 3 && behaviorData.centerClickRatio >= 0.75) {
      addFinding(findings, "CDP/Puppeteer弱信号", "点击落点高度集中在元素中心", "自动化工具常默认点击元素几何中心，真人点击通常有更大落点噪声。", 8, "warn");
    }

    if (behaviorData.repeatedCoordinateClicks > 0) {
      addFinding(findings, "CDP/Puppeteer弱信号", "多次点击完全相同坐标", "重复坐标命中常见于脚本化动作或固定录制回放。", 6, "warn");
    }

    if (behaviorData.straightLineApproachClicks >= 2) {
      addFinding(findings, "CDP/Puppeteer弱信号", "点击前轨迹过于笔直", "多次接近目标的路径接近几何直线，适合作为弱风险信号。", 6, "warn");
    }

    if (behaviorData.untrustedEvents > 0) {
      addFinding(findings, "强信号", "发现非可信交互事件", "脚本 dispatchEvent 产生的事件通常 isTrusted=false。", 20, "danger");
    }

    if (behaviorData.clicks >= 4 && behaviorData.clickIntervalStddev > 0 && behaviorData.clickIntervalStddev < 80) {
      addFinding(findings, "行为", "点击节奏过于稳定", "多次点击间隔波动很低，可能是脚本节拍。", 7, "warn");
    }

    if (behaviorData.keydowns >= 8 && behaviorData.keyIntervalStddev > 0 && behaviorData.keyIntervalStddev < 35) {
      addFinding(findings, "行为", "输入节奏过于稳定", "连续输入间隔波动很低，可能是脚本注入或自动输入。", 8, "warn");
    }

    if (behaviorData.firstInteractionAtMs !== null && behaviorData.firstInteractionAtMs < 250) {
      addFinding(findings, "行为", "首个交互发生过快", "页面加载后极短时间内开始操作，适合作为弱风险信号。", 4, "info");
    }

    if (report.cdpSerializationProbe.consoleGetterHit || report.cdpSerializationProbe.errorStackGetterHit) {
      addFinding(findings, "Inspector/CDP", "console 序列化探针被触发", "页面对象被 console/CDP 读取时触发 getter，说明存在调试器或控制端读取对象预览的可能。", 8, "warn");
    }

    if (report.debuggerTimingProbe && report.debuggerTimingProbe.maxMs > 120) {
      addFinding(findings, "Inspector/CDP", "debugger 语句出现明显暂停", "debugger statement 执行耗时异常，可能存在已打开 DevTools 或已启用 Debugger 的控制端。", 12, "warn");
    }

    if (report.errorStackProbe && report.errorStackProbe.automationHints && report.errorStackProbe.automationHints.length) {
      addFinding(findings, "Inspector/CDP", "Error.stack 出现自动化相关帧", report.errorStackProbe.automationHints.join(" | "), 15, "warn");
    }

    if (report.debugPortProbe && report.debugPortProbe.reachablePorts && report.debugPortProbe.reachablePorts.length) {
      addFinding(findings, "Inspector/CDP", "发现常见本地 debug 端口可达", "可达端口: " + report.debugPortProbe.reachablePorts.join(", ") + "。这可能意味着浏览器开启了 remote debugging。", 18, "warn");
    }

    if (!findings.length) {
      addFinding(findings, "结论", "未发现明显自动化信号", "当前结果更接近普通人工浏览，但仍需要结合服务端网络和业务数据。", 0, "ok");
    }

    var score = findings.reduce(function (sum, finding) {
      return sum + finding.points;
    }, 0);
    score = Math.max(0, Math.min(100, score));
    return {
      score: score,
      classification: classify(score),
      findings: findings
    };
  }

  function classify(score) {
    if (score >= 71) {
      return { label: "high confidence automation", level: "danger" };
    }
    if (score >= 46) {
      return { label: "likely automation", level: "danger" };
    }
    if (score >= 21) {
      return { label: "suspicious", level: "warn" };
    }
    return { label: "human-like", level: "ok" };
  }

  function buildSummary(report) {
    return [
      { label: "自动化强信号", value: report.score.findings.filter(function (item) { return item.category === "强信号" && item.points > 0; }).length },
      { label: "一致性问题", value: report.score.findings.filter(function (item) { return item.category === "一致性"; }).length },
      { label: "Inspector/CDP信号", value: report.score.findings.filter(function (item) { return item.category === "CDP/Puppeteer弱信号" || item.category === "Inspector/CDP"; }).length },
      { label: "行为样本", value: report.behavior.moves + " moves / " + report.behavior.clicks + " clicks" }
    ];
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
      return '<article class="metric"><span>' + escapeHtml(metric.label) + '</span><strong>' + escapeHtml(metric.value) + '</strong></article>';
    }).join("");

    findingsEl.innerHTML = report.score.findings.map(function (finding) {
      return [
        '<article class="finding">',
        '<span class="tag">' + escapeHtml(finding.category) + '</span>',
        '<div><strong>' + escapeHtml(finding.title) + '</strong><p>' + escapeHtml(finding.detail) + '</p></div>',
        '<span class="points">+' + finding.points + '</span>',
        '</article>'
      ].join("");
    }).join("");

    rawEl.textContent = JSON.stringify(report, null, 2);
    document.getElementById("statusText").textContent = "检测完成，本页数据仅保存在当前浏览器。";
  }

  function escapeHtml(value) {
    return String(value)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  function runDetection() {
    document.getElementById("statusText").textContent = "正在采集信号...";
    return Promise.all([
      getHighEntropyValues(),
      getAudioHash(),
      runDebugPortProbe()
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
        iframeConsistency: getIframeConsistency(),
        nativeIntegrity: getNativeIntegrity(),
        graphics: {
          canvasHash: getCanvasHash(),
          webgl: getWebglInfo(),
          audioHash: values[1]
        },
        behavior: getBehaviorSnapshot()
      };
      report.score = scoreReport(report);
      lastReport = report;
      render(report);
      return report;
    });
  }

  function resetBehavior() {
    behavior.startedAt = performance.now();
    behavior.moves = 0;
    behavior.clicks = 0;
    behavior.wheels = 0;
    behavior.scrolls = 0;
    behavior.keydowns = 0;
    behavior.paste = 0;
    behavior.pointerSamples = [];
    behavior.clickTimes = [];
    behavior.clickDetails = [];
    behavior.keyIntervals = [];
    behavior.lastKeyAt = 0;
    behavior.firstInteractionAt = null;
    behavior.visibilityChanges = 0;
    behavior.noRecentPointerMoveClicks = 0;
    behavior.straightLineApproachClicks = 0;
    behavior.untrustedPointerMoves = 0;
    behavior.untrustedClicks = 0;
    behavior.untrustedKeys = 0;
    behavior.lastPointerMoveAt = 0;
    behavior.lastPointerPosition = null;
    runDetection();
  }

  function exportReport() {
    if (!lastReport) {
      return;
    }
    var blob = new Blob([JSON.stringify(lastReport, null, 2)], { type: "application/json" });
    var url = URL.createObjectURL(blob);
    var link = document.createElement("a");
    link.href = url;
    link.download = "automation-detection-report.json";
    document.body.appendChild(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
  }

  window.addEventListener("pointermove", function (event) {
    behavior.moves += 1;
    if (event.isTrusted === false) {
      behavior.untrustedPointerMoves = (behavior.untrustedPointerMoves || 0) + 1;
    }
    behavior.lastPointerMoveAt = performance.now();
    behavior.lastPointerPosition = {
      x: Math.round(event.clientX),
      y: Math.round(event.clientY)
    };
    markInteraction();
    pushLimited(behavior.pointerSamples, {
        t: Math.round(performance.now() - behavior.startedAt),
        x: Math.round(event.clientX),
        y: Math.round(event.clientY),
        type: event.pointerType || "unknown"
      }, 500);
  }, { passive: true });

  window.addEventListener("click", function (event) {
    behavior.clicks += 1;
    behavior.clickTimes.push(Math.round(performance.now()));
    if (event.isTrusted === false) {
      behavior.untrustedClicks = (behavior.untrustedClicks || 0) + 1;
    }
    var now = performance.now();
    var rect = event.target && event.target.getBoundingClientRect ? event.target.getBoundingClientRect() : null;
    var centerDistanceRatio = null;
    if (rect && rect.width > 0 && rect.height > 0) {
      var centerX = rect.left + rect.width / 2;
      var centerY = rect.top + rect.height / 2;
      centerDistanceRatio = Number((distance(event.clientX, event.clientY, centerX, centerY) / Math.max(1, Math.min(rect.width, rect.height))).toFixed(3));
    }
    var recentPointerMoveMs = behavior.lastPointerMoveAt ? Math.round(now - behavior.lastPointerMoveAt) : null;
    if (recentPointerMoveMs === null || recentPointerMoveMs > 1200) {
      behavior.noRecentPointerMoveClicks = (behavior.noRecentPointerMoveClicks || 0) + 1;
    }
    var straightness = getApproachStraightness(event.clientX, event.clientY);
    if (straightness !== null && straightness < 1.08) {
      behavior.straightLineApproachClicks = (behavior.straightLineApproachClicks || 0) + 1;
    }
    if (!behavior.clickDetails) {
      behavior.clickDetails = [];
    }
    pushLimited(behavior.clickDetails, {
      t: Math.round(now - behavior.startedAt),
      x: Math.round(event.clientX),
      y: Math.round(event.clientY),
      target: event.target && event.target.dataset ? event.target.dataset.probeTarget || event.target.tagName : event.target.tagName,
      isTrusted: event.isTrusted,
      detail: event.detail,
      recentPointerMoveMs: recentPointerMoveMs,
      centerDistanceRatio: centerDistanceRatio,
      approachStraightness: straightness
    }, 100);
    markInteraction();
    setTimeout(runDetection, 50);
  }, { passive: true });

  window.addEventListener("wheel", function () {
    behavior.wheels += 1;
    markInteraction();
  }, { passive: true });

  window.addEventListener("scroll", function () {
    behavior.scrolls += 1;
    markInteraction();
  }, { passive: true });

  window.addEventListener("keydown", function (event) {
    var now = performance.now();
    behavior.keydowns += 1;
    if (event.isTrusted === false) {
      behavior.untrustedKeys = (behavior.untrustedKeys || 0) + 1;
    }
    if (behavior.lastKeyAt) {
      behavior.keyIntervals.push(Math.round(now - behavior.lastKeyAt));
    }
    behavior.lastKeyAt = now;
    markInteraction();
    setTimeout(runDetection, 50);
  }, { passive: true });

  window.addEventListener("paste", function () {
    behavior.paste += 1;
    markInteraction();
  }, { passive: true });

  document.addEventListener("visibilitychange", function () {
    behavior.visibilityChanges += 1;
  });

  document.getElementById("runBtn").addEventListener("click", runDetection);
  document.getElementById("exportBtn").addEventListener("click", exportReport);
  document.getElementById("resetBehaviorBtn").addEventListener("click", resetBehavior);

  runDetection();
  setInterval(runDetection, 5000);
}());
