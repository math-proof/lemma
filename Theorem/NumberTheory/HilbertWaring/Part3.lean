/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Def.Combinatorics.Schnirelmann
import Lemma.Finset.Schnirelmann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Def.NumberTheory.HilbertWaring.Part4
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_pairFiber_card_real_le (H M : ℕ) (hHM : H ≤ M)
    (h₁ h₂ : hwSigned H) (n : ℤ) :
    (#(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n) : ℝ) ≤
      4 * (M + 1) *
        (if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n.natAbs then
          ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
            max (h₁.2.val + 1) (h₂.2.val + 1) else 0) := by
  let a := hwSignedVal H h₁
  let b := hwSignedVal H h₂
  have ha0 : a ≠ 0 := hw_signedVal_ne_zero H h₁
  have hb0 : b ≠ 0 := hw_signedVal_ne_zero H h₂
  have haM : a.natAbs ≤ M := (hw_signedVal_natAbs_le H h₁).trans hHM
  have hbM : b.natAbs ≤ M := (hw_signedVal_natAbs_le H h₂).trans hHM
  have hgcd : a.gcd b = (h₁.2.val + 1).gcd (h₂.2.val + 1) := by
    simp [a, b, Int.gcd_eq_natAbs]
  split_ifs with hdvd
  · have hmax0 : (0 : ℝ) < max a.natAbs b.natAbs := by positivity
    have hmax : max a.natAbs b.natAbs =
        max (h₁.2.val + 1) (h₂.2.val + 1) := by simp [a, b]
    rw [← hgcd, ← hmax]
    rw [show (4 : ℝ) * (M + 1) * ((a.gcd b : ℝ) / max a.natAbs b.natAbs) =
        (4 * (M + 1) * (a.gcd b : ℝ)) / max a.natAbs b.natAbs by ring]
    rw [le_div_iff₀ hmax0]
    exact_mod_cast hw_pairFiber_card_mul_max_le M ha0 hb0 haM hbM
  · have hempty : hwPairFiber M a b n = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro p hp
      apply hdvd
      rw [← hgcd]
      exact hw_gcd_dvd_natAbs_of_pairFiber_nonempty M ⟨p, hp⟩
    have hempty' : hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n = ∅ := by
      simpa [a, b] using hempty
    simp [hempty']

end MathlibExt.NumberTheory.HilbertWaringWanted
