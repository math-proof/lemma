import Mathlib
import Initialize.Tactic.Attr.Basic
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Algebra.TensorProduct MvPolynomial
open scoped TensorProduct
open Algebra.TensorProduct MvPolynomial


namespace Separatedness

/--
[affine_isSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Separatedness.lean)
-/
@[path]
lemma affine_isSeparated
  {X : Scheme.{u}}
  [IsAffine X] :
-- imply
  X.IsSeparated :=
-- proof
  inferInstance

end Separatedness

namespace Separatedness

/--
[prop9_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Separatedness.lean)
-/
@[path]
lemma prop9_forward
  {X : Scheme.{u}}
  [X.IsSeparated]
  {U V : X.Opens}
-- given
  (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) :
-- imply
  IsAffineOpen (U ⊓ V) :=
-- proof
  hU.inf hV

end Separatedness

namespace Separatedness

/--
[affine_diagonal_iff_affine_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Separatedness.lean)
-/
@[path]
lemma affine_diagonal_iff_affine_intersection
  {X : Scheme.{u}} :
-- imply
  IsAffineHom (pullback.diagonal (terminal.from X)) ↔ ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) := by
-- proof
  constructor
  · intro h U V hU hV
    haveI := h
    exact hU.inf hV
  · intro h
    rw [isAffineHom_diagonal_iff]
    intro U _ V₁ _ V₂ _ hV₁ hV₂
    exact h V₁ V₂ hV₁ hV₂

end Separatedness

namespace Separatedness

/--
[prop9_separated_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Separatedness.lean)
-/
@[path]
lemma prop9_separated_iff
  {X : Scheme.{u}} :
-- imply
  X.IsSeparated ↔ (∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) ∧ (∀ (W : (pullback (terminal.from X) (terminal.from X)).Opens), IsAffineOpen W → Function.Surjective ((pullback.diagonal (terminal.from X)).app W)) := by
-- proof
  rw [Scheme.isSeparated_iff, isSeparated_iff,
    isClosedImmersion_iff_isAffineHom]
  constructor
  · rintro ⟨hAff, hSurj⟩
    exact ⟨affine_diagonal_iff_affine_intersection.mp hAff, hSurj⟩
  · rintro ⟨hAff, hSurj⟩
    exact ⟨affine_diagonal_iff_affine_intersection.mpr hAff, hSurj⟩

end Separatedness

namespace Separatedness

/--
[tmul_one_sub_one_tmul_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Separatedness.lean)
-/
@[path]
lemma tmul_one_sub_one_tmul_mul
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  {a b : A} :
-- imply
  (a * b) ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] (a * b) = (a ⊗ₜ[R] (1 : A)) * (b ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] b) + (a ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] a) * ((1 : A) ⊗ₜ[R] b) := by
-- proof
  simp only [mul_sub, sub_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  abel

end Separatedness

namespace Separatedness

/--
[tmul_one_sub_one_tmul_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Separatedness.lean)
-/
@[path]
lemma tmul_one_sub_one_tmul_add
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  {a b : A} :
-- imply
  (a + b) ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] (a + b) = (a ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] a) + (b ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] b) := by
-- proof
  simp [TensorProduct.add_tmul, TensorProduct.tmul_add]; abel

end Separatedness

namespace Separatedness

/--
[tmul_one_sub_one_tmul_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Separatedness.lean)
-/
@[path]
lemma tmul_one_sub_one_tmul_algebraMap
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  {r : R} :
-- imply
  (algebraMap R A r) ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] (algebraMap R A r) = 0 := by
-- proof
  rw [Algebra.algebraMap_eq_smul_one, sub_eq_zero]
  exact TensorProduct.CompatibleSMul.smul_tmul r 1 1

end Separatedness


-- created on 2026-10-23
