"""Accessible, reusable rendering for the blueprint's formula-driven figures."""

from pathlib import Path

from plasTeX import Command
from plasTeX.PackageResource import PackageJs, PackageResource, PackageTemplateDir


PACKAGE_DIR = Path(__file__).resolve().parent
BLUEPRINT_SRC = PACKAGE_DIR.parent
GENERATED_DIR = BLUEPRINT_SRC / "figures" / "generated"


class FigureAsset(PackageResource):
    outdir = "figures"
    copy = True


class gluckfigure(Command):
    """A numbered figure with a stable web-component and asset identifier."""

    args = "figureId:str caption alt:str label:str"
    counter = "figure"
    blockType = True

    def invoke(self, tex):
        result = super().invoke(tex)
        self.title = self.attributes["caption"]
        self.ownerDocument.context.label(self.attributes["label"], self)
        return result


def ProcessOptions(options, document):
    resources = [
        PackageTemplateDir(path=PACKAGE_DIR / "templates"),
        PackageJs(path=PACKAGE_DIR / "static" / "gluck-figures.js"),
        FigureAsset(path=GENERATED_DIR / "figures.json"),
    ]
    resources.extend(
        FigureAsset(path=GENERATED_DIR / f"{figure_id}.svg")
        for figure_id in (
            "euclidean-closure",
            "euclidean-gluck-reconstructions",
            "discrete-gluck-menger-reconstructions",
            "discrete-menger-bridge",
            "menger-curvature-spaceforms",
            "menger-curvature-profiles-spaceforms",
            "euclidean-dahlberg-reconstructions",
            "sphere-stereographic",
            "sphere-reconstructions",
            "hyperbolic-escape",
            "hyperbolic-reconstructions",
            "winding-angle-lift",
            "winding-error-map",
            "degree-one-reparametrization",
            "hyperbolic-geometry-atlas",
            "hyperbolic-flow-stability",
            "hyperbolic-closing-engine",
            "hyperbolic-simplicity",
            "spaceform-unification",
        )
    )
    document.addPackageResource(resources)
