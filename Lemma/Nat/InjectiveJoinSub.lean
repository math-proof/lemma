import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.SphericalBuilding.GLnApartmentIsoUnconditional
open GLnBuilding


namespace Definitions
end Definitions
/--
[joinSub_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnApartmentIsoUnconditional.lean)
-/
@[path]
private lemma joinSub_injective_eq
  [Field k]
  {n : ℕ}
  {F : Frame k n} :
-- imply
  Function.Injective (joinSub F) := by
-- proof
  apply GLnBuilding.joinSub_injective F

/--
[joinSub_isCompatible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnApartmentIsoUnconditional.lean)
-/
@[path]
private lemma joinSub_isCompatible_eq
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S : Finset (Fin n)} :
-- imply
  F.IsCompatible k n (joinSub F S) := by
-- proof
  apply GLnBuilding.joinSub_isCompatible F S

/--
[extractFinset_of_joinSub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnApartmentIsoUnconditional.lean)
-/
@[path]
private lemma extractFinset_of_joinSub_eq
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {S : Finset (Fin n)} :
-- imply
  extractFinset k n F (joinSub F S) = S := by
-- proof
  apply GLnBuilding.extractFinset_of_joinSub F S

/--
[joinSub_extractFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnApartmentIsoUnconditional.lean)
-/
@[path]
private lemma joinSub_extractFinset_eq
  [Field k]
  {n : ℕ}
  {F : Frame k n}
  {V : Submodule k (Vec k n)}
-- given
  (h : F.IsCompatible k n V) :
-- imply
  joinSub F (extractFinset k n F V) = V := by
-- proof
  apply GLnBuilding.joinSub_extractFinset F V h


-- created on 2026-10-24
