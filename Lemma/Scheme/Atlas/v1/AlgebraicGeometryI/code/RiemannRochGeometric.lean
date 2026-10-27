import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeometric
open AlgebraicGeometry CategoryTheory RiemannRochGeometric


namespace RiemannRochGeometric

/--
[additive_hom_determined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeometric.lean)
-/
@[path]
lemma additive_hom_determined
  {k : Type}
  [Field k]
  {f : ℤ × ℤ →+ ℤ}
  {p : ℤ × ℤ} :
-- imply
  f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
-- proof
  obtain ⟨r, d⟩ := p
  show f (r, d) = r * f (1, 0) + d * f (0, 1)
  have h1 : (r, d) = (r, 0) + (0, d) := by ext <;> simp
  rw [h1, map_add]
  congr 1
  · have : (r, (0 : ℤ)) = r • (1, 0) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]
  · have : ((0 : ℤ), d) = d • (0, 1) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]

end RiemannRochGeometric

namespace RiemannRochGeometric

/--
[theorem_24_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeometric.lean)
-/
@[path]
lemma theorem_24_2
  {k : Type}
  [Field k]
  {C : SmoothCurveWithCohomology k}
  {F : C.X.Modules} :
-- imply
  C.eulerChar F = C.degree F + C.sheafRank F * (1 - (C.arithmeticGenus : ℤ)) := by
-- proof
  unfold SmoothCurveWithCohomology.eulerChar
  rw [C.chi_eq_chiK0 F]
  rw [additive_hom_determined C.chiK0 (C.sheafRank F, C.degree F)]
  rw [C.chi_structureSheaf, C.chi_skyscraper]
  ring

end RiemannRochGeometric

namespace RiemannRochGeometric

/--
[theorem_24_2_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeometric.lean)
-/
@[path]
lemma theorem_24_2_alt
  {k : Type}
  [Field k]
  {C : SmoothCurveWithCohomology k}
  {F : C.X.Modules} :
-- imply
  C.eulerChar F = C.degree F - C.sheafRank F * ((C.arithmeticGenus : ℤ) - 1) := by
-- proof
  have h := theorem_24_2 C F
  linarith

end RiemannRochGeometric

namespace RiemannRochGeometric

/--
[theorem_24_2_rank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeometric.lean)
-/
@[path]
lemma theorem_24_2_rank_one
  {k : Type}
  [Field k]
  {C : SmoothCurveWithCohomology k}
  {F : C.X.Modules}
-- given
  (hrank : C.sheafRank F = 1) :
-- imply
  C.eulerChar F = C.degree F + 1 - (C.arithmeticGenus : ℤ) := by
-- proof
  have h := theorem_24_2 C F
  rw [hrank] at h
  linarith

end RiemannRochGeometric

namespace RiemannRochGeometric

/--
[theorem_24_2_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeometric.lean)
-/
@[path]
lemma theorem_24_2_torsion
  {k : Type}
  [Field k]
  {C : SmoothCurveWithCohomology k}
  {F : C.X.Modules}
-- given
  (hrank : C.sheafRank F = 0) :
-- imply
  C.eulerChar F = C.degree F := by
-- proof
  have h := theorem_24_2 C F
  rw [hrank] at h
  linarith

end RiemannRochGeometric

namespace RiemannRochGeometric

/--
[theorem_24_2_structure_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeometric.lean)
-/
@[path]
lemma theorem_24_2_structure_sheaf
  {k : Type}
  [Field k]
  {C : SmoothCurveWithCohomology k}
  {F : C.X.Modules}
-- given
  (hrank : C.sheafRank F = 1)
  (hdeg : C.degree F = 0) :
-- imply
  C.eulerChar F = 1 - (C.arithmeticGenus : ℤ) := by
-- proof
  have h := theorem_24_2 C F
  rw [hrank, hdeg] at h
  linarith
end RiemannRochGeometric



-- created on 2026-10-23
