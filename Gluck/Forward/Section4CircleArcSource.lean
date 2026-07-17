/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Section4CircleArcPaperSource
import Gluck.Forward.Section4ThreeContactCertificate
import Gluck.Forward.Section4TwoContactArc

/-!
# The source-free oriented circle arc in Dahlberg Section 4

The minimal circle has at least two polygonal contacts.  Exactly two contacts
are antipodal, while three or more contacts supply the ordered complementary
arc through the three-contact orientation anchor.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- The oriented complementary-circle arc required by the finite Section 4
splice follows from the two-contact and three-contact constructions. -/
theorem dahlbergE2_orientedCircleArcSource :
    DahlbergE2OrientedCircleArcSource := by
  intro n _ hn v O R hsimple _hregular hΔ hR run
  have htwo : 2 ≤ (circleContactSet v O R).card :=
    two_le_card_circleContactSet_of_minimalEnclosingDiskR2
      hΔ hR (mem_circleContactSet.mp run.contact)
  by_cases hthree : 3 ≤ (circleContactSet v O R).card
  · exact run.nonempty_circleArcCertificate_of_three_contacts
      hsimple hΔ hR hthree
  · have hcard : (circleContactSet v O R).card = 2 := by omega
    exact run.circleArcCertificate_of_contactSet_card_eq_two
      hsimple hΔ hR hcard

end Gluck.Forward
