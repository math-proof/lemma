import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff
open GrothendieckBirkhoff


namespace GrothendieckBirkhoff

/--
[eulerCharP1_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma eulerCharP1_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  eulerCharP1 k n = n + 1 :=
-- proof
  SheafCohomology.euler_characteristic k n

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[eulerCharP1_structure_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma eulerCharP1_structure_sheaf
  {k : Type}
  [Field k] :
-- imply
  eulerCharP1 k 0 = 1 := by
-- proof
  rw [eulerCharP1_eq]; ring

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[genusP1_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma genusP1_eq_zero
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (SheafCohomology.H1 k 0) = 0 :=
-- proof
  SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[genus_plane_curve_line](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma genus_plane_curve_line
-- imply
  genus_plane_curve 1 = 0 := by
-- proof
decide

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[genus_plane_curve_conic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma genus_plane_curve_conic
-- imply
  genus_plane_curve 2 = 0 := by
-- proof
decide

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[genus_plane_curve_cubic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma genus_plane_curve_cubic
-- imply
  genus_plane_curve 3 = 1 := by
-- proof
decide

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[genus_plane_curve_quartic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma genus_plane_curve_quartic
-- imply
  genus_plane_curve 4 = 3 := by
-- proof
decide

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[split_bundle_euler_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma split_bundle_euler_char
  {k : Type}
  [Field k]
  {n : ℕ}
  {degrees : Fin n → ℤ} :
-- imply
  ∑ i, eulerCharP1 k (degrees i) = ∑ i, (degrees i + 1) := by
-- proof
  congr 1; ext i; exact eulerCharP1_eq k (degrees i)

end GrothendieckBirkhoff

namespace GrothendieckBirkhoff

/--
[split_bundle_rr_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean)
-/
@[path]
lemma split_bundle_rr_P1
  {k : Type}
  [Field k]
  {n : ℕ}
  {degrees : Fin n → ℤ} :
-- imply
  ∑ i, eulerCharP1 k (degrees i) = (∑ i, degrees i) + n := by
-- proof
  rw [split_bundle_euler_char]
  simp [Finset.sum_add_distrib, Finset.sum_const]

end GrothendieckBirkhoff


-- created on 2026-10-23
