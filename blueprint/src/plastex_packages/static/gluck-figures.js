class GluckCurveFigure extends HTMLElement {
  connectedCallback() {
    if (this.dataset.ready === "true") return;
    this.dataset.ready = "true";
    this.dataset.manifest = "figures/figures.json";
  }
}

if (!customElements.get("gluck-curve-figure")) {
  customElements.define("gluck-curve-figure", GluckCurveFigure);
}
