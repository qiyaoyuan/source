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
      lastPointerSamples: behavior.pointerSamples.slice(-12)
    };
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

    if (behaviorData.clicks >= 4 && behaviorData.clickIntervalStddev > 0 && behaviorData.clickIntervalStddev < 80) {
      addFinding(findings, "行为", "点击节奏过于稳定", "多次点击间隔波动很低，可能是脚本节拍。", 7, "warn");
    }

    if (behaviorData.keydowns >= 8 && behaviorData.keyIntervalStddev > 0 && behaviorData.keyIntervalStddev < 35) {
      addFinding(findings, "行为", "输入节奏过于稳定", "连续输入间隔波动很低，可能是脚本注入或自动输入。", 8, "warn");
    }

    if (behaviorData.firstInteractionAtMs !== null && behaviorData.firstInteractionAtMs < 250) {
      addFinding(findings, "行为", "首个交互发生过快", "页面加载后极短时间内开始操作，适合作为弱风险信号。", 4, "info");
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
      { label: "运行时/图形问题", value: report.score.findings.filter(function (item) { return item.category === "运行时" || item.category === "图形"; }).length },
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
      getAudioHash()
    ]).then(function (values) {
      var report = {
        generatedAt: new Date().toISOString(),
        location: location.href,
        navigator: getNavigatorData(),
        highEntropyUserAgentData: values[0],
        environment: getEnvironmentData(),
        automationGlobals: getAutomationGlobals(),
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
    behavior.keyIntervals = [];
    behavior.lastKeyAt = 0;
    behavior.firstInteractionAt = null;
    behavior.visibilityChanges = 0;
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
    markInteraction();
    if (behavior.pointerSamples.length < 200) {
      behavior.pointerSamples.push({
        t: Math.round(performance.now() - behavior.startedAt),
        x: Math.round(event.clientX),
        y: Math.round(event.clientY),
        type: event.pointerType || "unknown"
      });
    }
  }, { passive: true });

  window.addEventListener("click", function () {
    behavior.clicks += 1;
    behavior.clickTimes.push(Math.round(performance.now()));
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

  window.addEventListener("keydown", function () {
    var now = performance.now();
    behavior.keydowns += 1;
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
