/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/PontryaginDual.lean -/

import Mathlib.NumberTheory.Padics.PadicIntegers
/-!
# Algebraic p-adic Pontryagin duals

This file defines the `ℤ_p`-linear dual `Hom(·, ℚ_p / ℤ_p)` and its
contragredient group action. No topology or continuity condition is imposed.
-/


namespace MetaMathlibExt

/-- The additive quotient `ℚ_p / ℤ_p`, represented using the canonical algebra map. -/
noncomputable abbrev PadicQuotientInt (p : ℕ) [Fact p.Prime] :=
  ℚ_[p] ⧸ LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])

/-- The algebraic `ℤ_p`-linear Pontryagin dual with values in `ℚ_p / ℤ_p`. -/
noncomputable abbrev PadicPontryaginDual (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℤ_[p] A] :=
  A →ₗ[ℤ_[p]] PadicQuotientInt p

end MetaMathlibExt
