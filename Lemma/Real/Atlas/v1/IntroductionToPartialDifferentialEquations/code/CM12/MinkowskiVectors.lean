import Mathlib
import sympy.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM12.MinkowskiVectors
open Matrix MinkowskiVectors


namespace MinkowskiVectors

/--
[lorentz_preserves_inner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean)
-/
@[path]
lemma lorentz_preserves_inner
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X Y : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ) :
-- imply
  minkowskiInner n (Λ *ᵥ X) (Λ *ᵥ Y) = minkowskiInner n X Y := by
-- proof
  simp only [minkowskiInner]
  rw [mulVec_mulVec]
  rw [dotProduct_mulVec (Λ *ᵥ X) (minkowskiMetric n * Λ) Y]
  rw [vecMul_mulVec Λ (minkowskiMetric n * Λ) X]
  rw [← Matrix.mul_assoc, hΛ]
  rw [← dotProduct_mulVec]

end MinkowskiVectors

namespace MinkowskiVectors

/--
[lorentz_preserves_timelike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean)
-/
@[path]
lemma lorentz_preserves_timelike
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsTimelike n X) :
-- imply
  IsTimelike n (Λ *ᵥ X) := by
-- proof
  unfold IsTimelike at *
  rwa [lorentz_preserves_inner hΛ]

end MinkowskiVectors

namespace MinkowskiVectors

/--
[lorentz_preserves_spacelike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean)
-/
@[path]
lemma lorentz_preserves_spacelike
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsSpacelike n X) :
-- imply
  IsSpacelike n (Λ *ᵥ X) := by
-- proof
  unfold IsSpacelike at *
  rwa [lorentz_preserves_inner hΛ]

end MinkowskiVectors

namespace MinkowskiVectors

/--
[lorentz_preserves_null](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean)
-/
@[path]
lemma lorentz_preserves_null
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsNull n X) :
-- imply
  IsNull n (Λ *ᵥ X) := by
-- proof
  unfold IsNull at *
  rwa [lorentz_preserves_inner hΛ]

end MinkowskiVectors

namespace MinkowskiVectors

/--
[lorentz_preserves_causal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean)
-/
@[path]
lemma lorentz_preserves_causal
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ)
  (hX : IsCausal n X) :
-- imply
  IsCausal n (Λ *ᵥ X) := by
-- proof
  cases hX with
  | inl h => exact Or.inl (lorentz_preserves_timelike hΛ h)
  | inr h => exact Or.inr (lorentz_preserves_null hΛ h)

end MinkowskiVectors

namespace MinkowskiVectors

/--
[lorentz_preserves_causal_character](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean)
-/
@[path]
lemma lorentz_preserves_causal_character
  {n : ℕ}
  {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {X : Fin (n + 1) → ℝ}
-- given
  (hΛ : IsLorentzTransformation n Λ) :
-- imply
  (IsTimelike n X → IsTimelike n (Λ *ᵥ X)) ∧ (IsSpacelike n X → IsSpacelike n (Λ *ᵥ X)) ∧ (IsNull n X → IsNull n (Λ *ᵥ X)) :=
-- proof
  ⟨fun h => lorentz_preserves_timelike hΛ h,
    fun h => lorentz_preserves_spacelike hΛ h,
    fun h => lorentz_preserves_null hΛ h⟩

end MinkowskiVectors


-- created on 2026-10-23
