/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4CircleArc

/-!
# The global Section 4 circle-arc certificate

The topological part of Dahlberg's Section 4 argument has exactly three
outputs: the completion arc spans at least a semicircle, and the first and
last retained chain edges strictly support the opposite endpoint.  Packaging
those outputs separately keeps the subsequent mesh construction entirely
finite and analytic.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- Global geometry of the positive run and its complementary minimal-circle
arc.  The embedded `Section4CircleArcCertificate` contains the ordered endpoint
parameters and the `π` lower bound; the two additional fields are the endpoint
support facts used by the strict form of Dahlberg's Lemma 10. -/
structure Section4SupportedCircleArcCertificate {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)
    extends Section4CircleArcCertificate run where
  left_support : 0 < crossR2
    (run.point run.chainStart) (run.point run.a) (run.point (run.b + 1))
  right_support : 0 < crossR2
    (run.point run.b) (run.point (run.b + 1)) (run.point run.chainStart)

end Gluck.Forward
