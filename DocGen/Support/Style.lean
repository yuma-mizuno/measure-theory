import DocGen.Support.Common

def pageThemeCss := r#"
:root {
  --mv-paper: #fffaf2;
  --mv-paper-2: #f8eee2;
  --mv-ink: #2b2731;
  --mv-muted: #6e6661;
  --mv-accent: #d98a6d;
  --mv-accent-2: #d9ad66;
  --mv-accent-3: #8db29a;
  --mv-panel: rgba(255, 255, 255, 0.8);
  --mv-line: rgba(43, 39, 49, 0.12);
  --mv-shadow: 0 18px 42px rgba(48, 37, 30, 0.1);
}

body {
  color: var(--mv-ink);
  background:
    radial-gradient(circle at top left, rgba(217, 138, 109, 0.14), transparent 28%),
    radial-gradient(circle at top right, rgba(217, 173, 102, 0.14), transparent 26%),
    linear-gradient(180deg, #fffaf3 0%, #fffefb 45%, #fbf4ea 100%);
  font-family: "Avenir Next", "Montserrat", "Trebuchet MS", sans-serif;
}

body::before {
  content: "";
  position: fixed;
  inset: 0;
  pointer-events: none;
  background-image:
    linear-gradient(rgba(255,255,255,0.4) 1px, transparent 1px),
    linear-gradient(90deg, rgba(255,255,255,0.35) 1px, transparent 1px);
  background-size: 28px 28px;
  opacity: 0.26;
}

header {
  position: sticky;
  top: 0;
  z-index: 20;
  backdrop-filter: blur(16px);
  background: rgba(253, 248, 241, 0.82);
  border-bottom: 1px solid rgba(31, 34, 51, 0.08);
}

.header-title h1,
.toc-title h1,
main section > h1 {
  font-family: "Recoleta", "Georgia", serif;
  letter-spacing: -0.02em;
  color: #312a2a;
}

.header-title h1,
.toc-title h1 {
  font-size: clamp(1.05rem, 1rem + 0.6vw, 1.45rem);
}

#toc {
  background: rgba(252, 246, 239, 0.94);
  border-right: 1px solid rgba(43, 39, 49, 0.08);
  backdrop-filter: blur(18px);
}

#toc .split-toc,
#toc .split-toc.book {
  border-radius: 18px;
  background: rgba(255, 255, 255, 0.6);
  box-shadow: inset 0 1px 0 rgba(255,255,255,0.6);
}

#toc a,
.prev-next-buttons a,
main a {
  color: #a85646;
  text-decoration-thickness: 0.08em;
  text-underline-offset: 0.15em;
}

#toc a:hover,
.prev-next-buttons a:hover,
main a:hover {
  color: #7c3d35;
}

main .content-wrapper {
  padding-top: 1.2rem;
}

main section {
  background: var(--mv-panel);
  border: 1px solid rgba(255,255,255,0.45);
  border-radius: 28px;
  box-shadow: var(--mv-shadow);
  padding: clamp(1.1rem, 2vw, 2rem);
}

main section > h1 {
  font-size: clamp(1.8rem, 1.5rem + 1vw, 2.6rem);
  line-height: 1.05;
  margin-bottom: 1.2rem;
}

main p,
main li {
  color: #2f3451;
  line-height: 1.78;
}

.prev-next-buttons .local-button {
  border-radius: 999px;
  border: 1px solid rgba(31, 34, 51, 0.08);
  background: rgba(255,255,255,0.72);
  box-shadow: 0 10px 24px rgba(48, 37, 30, 0.06);
}

.prev-next-buttons .local-button:hover {
  transform: translateY(-1px);
}

main code {
  font-family: "Iosevka Web", "IBM Plex Mono", "SFMono-Regular", monospace;
}

@media (max-width: 900px) {
  main section {
    border-radius: 22px;
    padding: 1rem;
  }
}
"#

def statementBlockCss := r#"
.mv-statement {
  --mv-statement-bg: rgba(255, 255, 255, 0.84);
  --mv-statement-border: var(--mv-line);
  --mv-statement-accent-start: var(--mv-accent);
  --mv-statement-accent-end: #ff8b7a;
  margin: 1rem 0 1.1rem 0;
  padding: 0.95rem 1rem 0.8rem 1rem;
  position: relative;
  border: 1px solid var(--mv-statement-border);
  background: var(--mv-statement-bg);
  border-radius: 22px;
  box-shadow: 0 16px 30px rgba(48, 37, 30, 0.08);
}

.mv-statement::before {
  content: "";
  position: absolute;
  left: 1rem;
  top: -0.45rem;
  width: 72px;
  height: 8px;
  border-radius: 999px;
  background:
    linear-gradient(
      90deg,
      var(--mv-statement-accent-start),
      var(--mv-statement-accent-end)
    );
}

.mv-statement-title {
  margin: 0 0 0.55rem 0;
  color: #342c2b;
  font-family: "Avenir Next Condensed", "Avenir Next", "Trebuchet MS", sans-serif;
  font-size: 1rem;
  font-style: normal;
  font-weight: 700;
  letter-spacing: 0.01em;
}

.mv-statement-body {
  font-style: normal;
}

.mv-statement code {
  font-family: "Iosevka Web", "IBM Plex Mono", "SFMono-Regular", monospace;
}

.mv-statement-body > :first-child {
  margin-top: 0;
}

.mv-statement-body > :last-child {
  margin-bottom: 0;
}

@media (max-width: 900px) {
  .mv-statement {
    border-radius: 18px;
  }
}
"#

def languageSwitcherCss := r#"
.mv-lang-switch {
  position: fixed;
  left: 1rem;
  bottom: 1rem;
  z-index: 30;
  pointer-events: auto;
}

.mv-lang-trigger {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  gap: 0.3rem;
  padding: 0.26rem 0.62rem;
  border-radius: 999px;
  border: 1px solid rgba(43, 39, 49, 0.08);
  background: rgba(255, 255, 255, 0.52);
  color: rgba(80, 68, 62, 0.82);
  font-size: 0.74rem;
  font-weight: 600;
  line-height: 1;
  box-shadow: 0 8px 18px rgba(48, 37, 30, 0.05);
  transition: background 120ms ease, color 120ms ease, border-color 120ms ease, box-shadow 120ms ease;
  cursor: pointer;
}

.mv-lang-trigger::after {
  content: "";
  width: 0.38rem;
  height: 0.38rem;
  border-right: 1.5px solid currentColor;
  border-bottom: 1.5px solid currentColor;
  transform: translateY(-0.08rem) rotate(45deg);
  opacity: 0.7;
  transition: transform 120ms ease;
}

.mv-lang-trigger:hover,
.mv-lang-switch.is-open .mv-lang-trigger {
  background: rgba(255, 255, 255, 0.7);
  color: #7c3d35;
  border-color: rgba(168, 86, 70, 0.14);
}

.mv-lang-switch.is-open .mv-lang-trigger::after {
  transform: translateY(0.04rem) rotate(-135deg);
}

.mv-lang-menu {
  position: absolute;
  bottom: calc(100% + 0.45rem);
  left: 0;
  min-width: 7.2rem;
  padding: 0.3rem;
  display: none;
  flex-direction: column;
  gap: 0.14rem;
  border: 1px solid rgba(43, 39, 49, 0.08);
  border-radius: 14px;
  background: rgba(255, 251, 247, 0.97);
  box-shadow: 0 14px 30px rgba(48, 37, 30, 0.12);
  backdrop-filter: blur(16px);
}

.mv-lang-switch.is-open .mv-lang-menu {
  display: flex;
}

.mv-lang-link {
  display: block;
  padding: 0.42rem 0.62rem;
  border-radius: 10px;
  color: rgba(80, 68, 62, 0.9);
  font-size: 0.78rem;
  font-weight: 500;
  line-height: 1.15;
  text-decoration: none;
  white-space: nowrap;
  transition: background 120ms ease, color 120ms ease;
}

.mv-lang-link:hover {
  background: rgba(217, 138, 109, 0.1);
  color: #7c3d35;
}

.mv-lang-link.is-active {
  background: rgba(217, 138, 109, 0.12);
  color: #7c3d35;
  pointer-events: none;
}

@media (max-width: 700px) {
  .mv-lang-switch {
    left: 0.75rem;
    bottom: 0.75rem;
  }

  .mv-lang-trigger {
    padding: 0.24rem 0.56rem;
    font-size: 0.72rem;
  }

  .mv-lang-menu {
    min-width: 6.5rem;
  }
}
"#

def languageSwitcherJs := r#"
(function () {
  const mountLanguageSwitcher = () => {
  const path = window.location.pathname;
  const search = window.location.search;
  const hash = window.location.hash;

  let currentLocale = "en";
  let enPath = path;
  let jaPath = path;

  if (path.includes("/ja/html-multi/")) {
    currentLocale = "ja";
    enPath = path.replace("/ja/html-multi/", "/html-multi/");
  } else if (path.includes("/html-multi/")) {
    jaPath = path.replace("/html-multi/", "/ja/html-multi/");
  } else {
    return;
  }

  const header = document.querySelector("header");
  const mount = document.body;
  if (!header || !mount || document.querySelector(".mv-lang-switch")) return;

  const nav = document.createElement("nav");
  nav.className = "mv-lang-switch";
  nav.setAttribute("aria-label", "Language switcher");

  const trigger = document.createElement("button");
  trigger.className = "mv-lang-trigger";
  trigger.type = "button";
  trigger.setAttribute("aria-haspopup", "menu");
  trigger.setAttribute("aria-expanded", "false");
  trigger.textContent = currentLocale === "ja" ? "言語" : "Language";

  const makeLink = (label, targetPath, active) => {
    const link = document.createElement("a");
    link.className = "mv-lang-link" + (active ? " is-active" : "");
    link.textContent = label;
    link.href = targetPath + search + hash;
    return link;
  };

  const menu = document.createElement("div");
  menu.className = "mv-lang-menu";
  menu.setAttribute("role", "menu");
  menu.appendChild(makeLink("English", enPath, currentLocale === "en"));
  menu.appendChild(makeLink("日本語", jaPath, currentLocale === "ja"));

  nav.appendChild(trigger);
  nav.appendChild(menu);
  mount.appendChild(nav);

  const closeMenu = () => {
    nav.classList.remove("is-open");
    trigger.setAttribute("aria-expanded", "false");
  };

  const openMenu = () => {
    nav.classList.add("is-open");
    trigger.setAttribute("aria-expanded", "true");
  };

  trigger.addEventListener("click", (event) => {
    event.stopPropagation();
    if (nav.classList.contains("is-open")) {
      closeMenu();
    } else {
      openMenu();
    }
  });

  document.addEventListener("click", (event) => {
    if (!nav.contains(event.target)) {
      closeMenu();
    }
  });

  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape") {
      closeMenu();
      trigger.blur();
    }
  });
  };

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", mountLanguageSwitcher, { once: true });
  } else {
    mountLanguageSwitcher();
  }
})();
"#

def leanCodeCss := r#"
.mv-lean-code {
  margin: 0.45rem 0 1.15rem 0;
  border: 1px solid rgba(43, 39, 49, 0.1);
  border-radius: 16px;
  background: rgba(248, 242, 234, 0.86);
  box-shadow: 0 10px 20px rgba(48, 37, 30, 0.05);
  overflow: hidden;
}

.mv-lean-code > summary {
  cursor: pointer;
  padding: 0.55rem 0.8rem;
  font-family: "Avenir Next", "Montserrat", "Trebuchet MS", sans-serif;
  font-size: 0.76rem;
  color: rgba(67, 59, 56, 0.74);
  letter-spacing: 0.03em;
  font-weight: 500;
  user-select: none;
  background: rgba(241, 233, 223, 0.72);
}

.mv-lean-code > summary:hover {
  background: rgba(236, 227, 217, 0.9);
}

.mv-lean-code-body {
  padding: 0.35rem 0.45rem 0.45rem 0.45rem;
  background: rgba(255, 252, 247, 0.88);
}

.mv-lean-code-body .hl.lean.block {
  border-radius: 12px;
  background: rgba(255, 255, 255, 0.7);
  color: #25222a;
}

.mv-lean-code-body a {
  color: #7a6dcb;
}

.mv-lean-code-body a:hover {
  color: #5f51b8;
}

.mv-lean-code-body .hl.lean.block .token,
.mv-lean-code-body .hl.lean.block .inter-text,
.mv-lean-code-body .hl.lean.block .unknown {
  color: inherit;
}

.mv-lean-decl {
  scroll-margin-top: 0.75rem;
}
"#

def leanDeclAnchorJs := r#"
(function () {
  const syncLeanDeclAnchors = () => {
    let activeWrapper = null;
    document.querySelectorAll(".mv-lean-decl[data-decl-id]").forEach((wrapper) => {
      const declId = wrapper.getAttribute("data-decl-id");
      if (!declId) return;
      const token = wrapper.querySelector('[id="' + declId + '"]');
      if (!token) return;
      if (!wrapper.id) wrapper.id = declId;
      if (token.id === declId) token.id = declId + "--token";
      if (decodeURIComponent(window.location.hash.slice(1)) === declId) {
        activeWrapper = wrapper;
      }
    });

    if (!activeWrapper) return;
    const codeBox = activeWrapper.closest("details.mv-lean-code");
    if (codeBox && !codeBox.open) codeBox.open = true;
    requestAnimationFrame(() => {
      activeWrapper.scrollIntoView({ block: "start", inline: "nearest" });
    });
  };

  const handleAnchorChange = () => {
    const hash = window.location.hash;
    if (!hash || hash.length <= 1) return;
    const target = document.getElementById(decodeURIComponent(hash.slice(1)));
    if (!target) return;
    const codeBox = target.closest("details.mv-lean-code");
    if (codeBox && !codeBox.open) codeBox.open = true;
  };

  const mountLeanDeclAnchors = () => {
    syncLeanDeclAnchors();
    handleAnchorChange();
    window.addEventListener("hashchange", () => {
      window.setTimeout(handleAnchorChange, 0);
    });
  };

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", mountLeanDeclAnchors, { once: true });
  } else {
    mountLeanDeclAnchors();
  }
})();
"#
