import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint.Part3
open Polynomial AlgebraicGeometry BlowupAtPoint


namespace BlowupAtPoint

/--
[properTransform_contains_preimage_away](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
lemma properTransform_contains_preimage_away
  [CommRing R]
  {I : Ideal R}
  {X Y : Scheme}
  {π : X ⟶ Y}
  {Z C : TopologicalSpace.Closeds Y.toTopCat} :
-- imply
  π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat)) ⊆ (properTransform π Z C : Set X.toTopCat) :=
-- proof
  subset_closure

end BlowupAtPoint

namespace BlowupAtPoint

/--
[reesAlgebra_monomial_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
lemma reesAlgebra_monomial_mem
  [CommRing R]
  {I : Ideal R}
  {n : ℕ}
  {a : R} :
-- imply
  monomial n a ∈ reesAlgebra I ↔ a ∈ I ^ n :=
-- proof
  reesAlgebra.monomial_mem

end BlowupAtPoint

namespace BlowupAtPoint

/--
[mem_reesAlgebra_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
lemma mem_reesAlgebra_char
  [CommRing R]
  {I : Ideal R}
  {f : R[X]} :
-- imply
  f ∈ reesAlgebra I ↔ ∀ i, f.coeff i ∈ I ^ i :=
-- proof
  mem_reesAlgebra_iff I f

end BlowupAtPoint

/--
[reesDecomposeComponent_coe_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
private lemma reesDecomposeComponent_coe_coe_eq
  [CommRing R]
  {I : Ideal R}
  {f : reesAlgebra I}
  {n : ℕ} :
-- imply
  ((reesDecomposeComponent I f n : ↥(reesAlgebra I)) : R[X]) = monomial n (f.val.coeff n) := by
-- proof
  apply BlowupAtPoint.reesDecomposeComponent_coe_coe I f n

/--
[coeff_coeAddMonoidHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
private lemma coeff_coeAddMonoidHom_eq
  [CommRing R]
  {I : Ideal R}
  {n : ℕ}
-- given
  (x : DirectSum ℕ (fun n => ↥(reesGrading I n))) :
-- imply
  ((DirectSum.coeAddMonoidHom (reesGrading I) x).val : R[X]).coeff n = ((x n).val : R[X]).coeff n := by
-- proof
  apply BlowupAtPoint.coeff_coeAddMonoidHom I x n

/--
[reesGrading_isInternal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
private lemma reesGrading_isInternal_eq
  [CommRing R]
  {I : Ideal R} :
-- imply
  DirectSum.IsInternal (reesGrading I) := by
-- proof
  apply BlowupAtPoint.reesGrading_isInternal I

/--
[reesGrading_one_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
private lemma reesGrading_one_mem_eq
  [CommRing R]
  {I : Ideal R} :
-- imply
  (1 : reesAlgebra I) ∈ reesGrading I 0 := by
-- proof
  apply BlowupAtPoint.reesGrading_one_mem I

/--
[reesGrading_mul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean)
-/
@[path]
private lemma reesGrading_mul_mem_eq
  [CommRing R]
  {I : Ideal R}
  {i j : ℕ}
  {fi fj : reesAlgebra I}
-- given
  (hi : fi ∈ reesGrading I i)
  (hj : fj ∈ reesGrading I j) :
-- imply
  fi * fj ∈ reesGrading I (i + j) := by
-- proof
  apply BlowupAtPoint.reesGrading_mul_mem I hi hj


-- created on 2026-10-23
