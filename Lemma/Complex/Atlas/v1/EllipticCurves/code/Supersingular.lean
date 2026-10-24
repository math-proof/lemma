import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
open OrdinarySupersingular Hasse


namespace Supersingular

/--
[trace_eq_zero_of_dvd_of_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Supersingular.lean)
-/
@[path]
lemma trace_eq_zero_of_dvd_of_sq_le
  {p : ℕ}
  {t : ℤ}
-- given
  (hp5 : (p : ℤ) ≥ 5)
  (hle : t ^ 2 ≤ 4 * (p : ℤ))
  (hdvd : (p : ℤ) ∣ t) :
-- imply
  t = 0 := by
-- proof
  obtain ⟨k, rfl⟩ := hdvd
  suffices k = 0 by simp [this]
  by_contra hk
  have hk_sq : 1 ≤ k ^ 2 := by
    have h0 := sq_pos_of_ne_zero hk
    omega
  have hle' : k ^ 2 * (p : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by
    have : (k * (p : ℤ)) ^ 2 = k ^ 2 * (p : ℤ) ^ 2 := by ring
    linarith
  have hp_sq : (p : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by nlinarith
  nlinarith

end Supersingular

namespace Supersingular

/--
[trace_sq_le_four_mul_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Supersingular.lean)
-/
@[path]
lemma trace_sq_le_four_mul_prime
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {E : WeierstrassCurve.Affine (ZMod p)} :
-- imply
  (Hasse.traceFrobenius E) ^ 2 ≤ 4 * (p : ℤ) := by
-- proof
  have hq : 0 < Fintype.card (ZMod p) := Fintype.card_pos
  have hsq := Hasse.trace_sq_le_four_mul_card E hq
  rw [ZMod.card] at hsq
  have h : ((Hasse.traceFrobenius E : ℤ) : ℝ) ^ 2 ≤ ((4 * (p : ℤ) : ℤ) : ℝ) := by
    push_cast; exact hsq
  exact_mod_cast h

end Supersingular

namespace Supersingular

/--
[trace_dvd_iff_trace_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Supersingular.lean)
-/
@[path]
lemma trace_dvd_iff_trace_eq_zero
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {E : WeierstrassCurve.Affine (ZMod p)}
-- given
  (hp3 : p > 3) :
-- imply
  (p : ℤ) ∣ Hasse.traceFrobenius E ↔ Hasse.traceFrobenius E = 0 := by
-- proof
  constructor
  · intro hdvd
    have hp5 : (p : ℤ) ≥ 5 := by
      have hprime := hp.out
      have : p ≠ 4 := by intro h; subst h; exact absurd hprime (by decide)
      omega
    exact trace_eq_zero_of_dvd_of_sq_le _ hp5
      (trace_sq_le_four_mul_prime p E) hdvd
  · intro h; rw [h]; exact dvd_zero _

end Supersingular

namespace Supersingular

/--
[trace_zero_iff_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Supersingular.lean)
-/
@[path]
lemma trace_zero_iff_card_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {E : WeierstrassCurve.Affine (ZMod p)} :
-- imply
  Hasse.traceFrobenius E = 0 ↔ (Hasse.numPoints E : ℤ) = (p : ℤ) + 1 := by
-- proof
  unfold Hasse.traceFrobenius Hasse.numPoints
  rw [ZMod.card]
  omega

end Supersingular

namespace Supersingular

/--
[supersingular_iff_trace_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Supersingular.lean)
-/
@[path]
lemma supersingular_iff_trace_eq_zero
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {E : WeierstrassCurve.Affine (ZMod p)}
-- given
  (hp3 : p > 3) :
-- imply
  IsSupersingular E p ↔ Hasse.traceFrobenius E = 0 := by
-- proof
  rw [isSupersingular_iff_trace_dvd p E]
  exact trace_dvd_iff_trace_eq_zero p hp3 E

end Supersingular

namespace Supersingular

/--
[supersingular_iff_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Supersingular.lean)
-/
@[path]
lemma supersingular_iff_card_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {E : WeierstrassCurve.Affine (ZMod p)}
-- given
  (hp3 : p > 3) :
-- imply
  IsSupersingular E p ↔ (Hasse.numPoints E : ℤ) = (p : ℤ) + 1 := by
-- proof
  rw [supersingular_iff_trace_eq_zero p hp3, trace_zero_iff_card_eq]

end Supersingular


-- created on 2026-10-23
