import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupDefinition.Part3
open Polynomial AlgebraicGeometry Blowup


namespace Blowup

/--
[properTransform_contains_preimage_away](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
-/
@[path]
lemma properTransform_contains_preimage_away
  [CommRing R]
  {I : Ideal R}
  {X Y : Scheme}
  {π : X ⟶ Y}
  {Z C : TopologicalSpace.Closeds Y.toTopCat} :
-- imply
  π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat)) ⊆ (properTransformSet π Z C : Set X.toTopCat) :=
-- proof
  subset_closure

end Blowup

namespace Blowup

/--
[properTransform_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
-/
@[path]
lemma properTransform_top
  [CommRing R]
  {I : Ideal R}
  {X Y : Scheme}
  {π : X ⟶ Y}
  {C : TopologicalSpace.Closeds Y.toTopCat} :
-- imply
  (properTransformSet π ⊤ C : Set X.toTopCat) = closure (π.base ⁻¹' (((⊤ : TopologicalSpace.Closeds Y.toTopCat) : Set Y.toTopCat) \ (C : Set Y.toTopCat))) := by
-- proof
  rfl
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedVariables false in

end Blowup

namespace Blowup

/--
[reesGrading_zero_iso_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
-/
@[path]
lemma reesGrading_zero_iso_base
  [CommRing R]
  {I : Ideal R} :
-- imply
  ∃ (e : ↥(reesGrading I 0) ≃+* R), True := by
-- proof
  refine ⟨?_, trivial⟩
  exact
  { toFun := fun f => (f.val : reesAlgebra I).val.coeff 0
    invFun := fun a => ⟨⟨monomial 0 a, by
      rw [mem_reesAlgebra_iff]; intro n
      by_cases h : n = 0
      · subst h; simp [Ideal.one_eq_top]
      · simp only [coeff_monomial, if_neg (Ne.symm h)]
        exact (I ^ n).zero_mem⟩, ⟨a, by simp [Ideal.one_eq_top], rfl⟩⟩
    left_inv := fun f => by
      apply Subtype.ext; apply Subtype.ext
      obtain ⟨a, _, ha'⟩ := f.property
      simp only; rw [ha', coeff_monomial_same]
    right_inv := fun a => by simp only [coeff_monomial_same]
    map_mul' := fun x y => by
      show (((x : reesAlgebra I).val * (y : reesAlgebra I).val)).coeff 0 = _
      obtain ⟨a, _, ha'⟩ := x.property
      obtain ⟨b, _, hb'⟩ := y.property
      rw [ha', hb', monomial_mul_monomial, coeff_monomial_same,
        coeff_monomial_same, coeff_monomial_same]
    map_add' := fun x y => by
      show (((x : reesAlgebra I).val + (y : reesAlgebra I).val)).coeff 0 = _
      rw [coeff_add] }

end Blowup

namespace Blowup

/--
[blowup_algebra_eq_rees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
-/
@[path]
lemma blowup_algebra_eq_rees
  [CommRing R]
  {I : Ideal R}
  {n : ℕ}
  {a : R}
-- given
  (ha : a ∈ I ^ n) :
-- imply
  (⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) ∈ reesGrading I n :=
-- proof
  ⟨a, ha, rfl⟩
end Blowup
/-- When the ideal `I` is finitely generated, the Rees algebra is of finite type as an algebra
over its degree-zero piece. -/
namespace Blowup
variable {R : Type*} [CommRing R] (I : Ideal R)
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The blow-up morphism `Bl_I(Spec R) ⟶ Spec R` is proper when `I` is finitely generated. -/
end Blowup


/--
[reesDecomposeComponent_coe_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
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
  apply Blowup.reesDecomposeComponent_coe_coe I f n

/--
[coeff_coeAddMonoidHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
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
  apply Blowup.coeff_coeAddMonoidHom I x n

/--
[reesGrading_isInternal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
-/
@[path]
private lemma reesGrading_isInternal_eq
  [CommRing R]
  {I : Ideal R} :
-- imply
  DirectSum.IsInternal (reesGrading I) := by
-- proof
  apply Blowup.reesGrading_isInternal I

/--
[reesGrading_one_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
-/
@[path]
private lemma reesGrading_one_mem_eq
  [CommRing R]
  {I : Ideal R} :
-- imply
  (1 : reesAlgebra I) ∈ reesGrading I 0 := by
-- proof
  apply Blowup.reesGrading_one_mem I

/--
[reesGrading_mul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean)
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
  apply Blowup.reesGrading_mul_mem I hi hj


-- created on 2026-10-23
