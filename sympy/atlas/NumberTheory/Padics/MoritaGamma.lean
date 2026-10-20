/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGamma.lean -/

import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Morita's p-adic gamma function

This file defines the finite values interpolated by Morita's p-adic gamma function and a
specification for its continuous extension to the p-adic integers.
-/

namespace MetaMathlibExt

/-- The finite value interpolated by Morita's p-adic gamma function.

For positive `n`, this is `(-1) ^ n` times the product of the positive integers below `n` that are
not divisible by `p`. The same formula gives `1` at zero. -/
noncomputable def moritaGammaNat (p n : ℕ) [Fact p.Prime] : PadicInt p :=
  (-1 : PadicInt p) ^ n *
    ∏ k ∈ (Finset.range n).filter (fun k => ¬p ∣ k), (k : PadicInt p)

@[simp]
theorem moritaGammaNat_zero (p : ℕ) [Fact p.Prime] :
    moritaGammaNat p 0 = 1 := by
  simp [moritaGammaNat]

/-- A continuous, unit-valued extension of Morita's finite p-adic gamma values. -/
def IsMoritaPadicGamma (p : ℕ) [Fact p.Prime]
    (Γ : C(PadicInt p, PadicInt p)) : Prop :=
  Γ 0 = 1 ∧
    (∀ n : ℕ, 0 < n → Γ (n : PadicInt p) = moritaGammaNat p n) ∧
    ∀ x : PadicInt p, IsUnit (Γ x)

theorem IsMoritaPadicGamma.zero_eq {p : ℕ} [Fact p.Prime]
    {Γ : C(PadicInt p, PadicInt p)} (hΓ : IsMoritaPadicGamma p Γ) :
    Γ 0 = 1 :=
  hΓ.1

theorem IsMoritaPadicGamma.natCast_eq {p : ℕ} [Fact p.Prime]
    {Γ : C(PadicInt p, PadicInt p)} (hΓ : IsMoritaPadicGamma p Γ)
    {n : ℕ} (hn : 0 < n) : Γ (n : PadicInt p) = moritaGammaNat p n :=
  hΓ.2.1 n hn

theorem IsMoritaPadicGamma.isUnit {p : ℕ} [Fact p.Prime]
    {Γ : C(PadicInt p, PadicInt p)} (hΓ : IsMoritaPadicGamma p Γ)
    (x : PadicInt p) : IsUnit (Γ x) :=
  hΓ.2.2 x

end MetaMathlibExt
