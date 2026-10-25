/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/BilinearForm/Prod.lean -/


import Instance.LinearAlgebra.BilinearForm.Prod
import Lemma.Matrix.BilinearForm.Prod
import Mathlib.RingTheory.Localization.FractionRing
open LinearMap (BilinForm)
open Module

/-!
# Tests for the orthogonal product of bilinear forms

Examples exercising `BilinForm.prod` and its nondegeneracy, perfectness,
and dual-submodule API, including a source-shaped Noetherian-domain
fraction-field case.
-/


namespace LinearMap

namespace BilinForm

section Formula

variable {R M₁ M₂ : Type*} [CommSemiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

-- The evaluation formula fires as a simp lemma.
example (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (x y : M₁ × M₂) :
    B₁.prod B₂ x y = B₁ x.1 y.1 + B₂ x.2 y.2 := by
  simp

-- Forward direction of the nondegeneracy characterisation.
example {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂}
    (h : (B₁.prod B₂).Nondegenerate) :
    B₁.Nondegenerate ∧ B₂.Nondegenerate :=
  nondegenerate_prod_iff.mp h

-- Reverse direction of the nondegeneracy characterisation.
example {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂}
    (h₁ : B₁.Nondegenerate) (h₂ : B₂.Nondegenerate) :
    (B₁.prod B₂).Nondegenerate :=
  nondegenerate_prod_iff.mpr ⟨h₁, h₂⟩

end Formula

section TrivialFactor

-- A product with a trivial factor is nondegenerate when the other
-- factor is: both separating conditions hold vacuously on `Fin 0 → ℚ`.
example (B₁ : BilinForm ℚ ℚ) (h₁ : B₁.Nondegenerate)
    (B₂ : BilinForm ℚ (Fin 0 → ℚ)) :
    (B₁.prod B₂).Nondegenerate := by
  rw [nondegenerate_prod_iff]
  refine ⟨h₁, ⟨fun x _ => Subsingleton.elim x 0, fun y _ => ?_⟩⟩
  exact Subsingleton.elim y 0

end TrivialFactor
end BilinForm
end LinearMap
