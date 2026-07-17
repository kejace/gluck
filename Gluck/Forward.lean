import Gluck.Forward.Dahlberg
import Gluck.Forward.Section4PositiveGap
import Gluck.Forward.Section4PositiveChain
import Gluck.Forward.Section4CircleSplice
import Gluck.Forward.Section4AuxiliaryConsumer
import Gluck.Forward.Section4AuxiliaryRadiusObstruction
import Gluck.Forward.Section4EndpointCurvature
import Gluck.Forward.Smooth
import Gluck.Forward.Euclidean

/-!
# Forward four-vertex theorems

This module re-exports only the active forward-theorem development:

* the smooth forward four-vertex theorem, sourced from `references/dahlberg.pdf`;
* the Euclidean discrete Dahlberg four-vertex theorem, sourced from
  `references/23.pdf`.

Space-form discrete, conformal-Menger, and non-Euclidean wrapper work has been
moved out to the separate `feat-deferred` worktree.
-/
