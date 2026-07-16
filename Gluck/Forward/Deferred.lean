import Gluck.Forward.Deferred.SpaceFormDiscrete
import Gluck.Forward.Deferred.Sphere
import Gluck.Forward.Deferred.Hyperbolic
import Gluck.Forward.Deferred.ConformalMenger
import Gluck.Forward.Deferred.Sources

/-!
# Deferred forward theorem work

This module re-exports the forward-theorem material that is intentionally not
part of the active `Gluck.Forward` API while the branch focuses on:

* smooth forward 4VT from `references/dahlberg.pdf`;
* Euclidean discrete D4VT from `references/23.pdf`.

The declarations here are parked under `Gluck.Forward.Deferred`; remaining
geometric source gates are allowed to stay as `sorry`s.
-/
