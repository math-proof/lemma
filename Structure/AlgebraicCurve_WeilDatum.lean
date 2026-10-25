import Mathlib
import Def.AlgebraicCurve_PlaceEvaluation

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in

structure WeilDatum (n : ℕ) where

  D₁ : Divisor K F

  D₂ : Divisor K F

  f₁ : F

  f₂ : F
  f₁_ne_zero : f₁ ≠ 0
  f₂_ne_zero : f₂ ≠ 0

  ord_f₁ : ∀ v : Place K F, v.ord f₁ = n * D₁ v

  ord_f₂ : ∀ v : Place K F, v.ord f₂ = n * D₂ v

  disjoint : ∀ v : Place K F, D₁ v = 0 ∨ D₂ v = 0

  rational : ∀ v : Place K F, D₁ v ≠ 0 ∨ D₂ v ≠ 0 → v.IsRational

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)


end WeilDatum

end AlgebraicCurve
