/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Abbrev.Dynamics.EventuallyPeriodicSequence
import Lemma.Set.EventuallyPeriodicSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Def.NumberTheory.ContinuedFractions.LagrangePeriodic.Part2
/-!
# Euler–Lagrange theorem on eventually periodic continued fractions

This file proves the Lagrange direction of the Euler–Lagrange characterization
of eventually periodic continued fractions: a real quadratic irrational has an
eventually periodic continued fraction
(`continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational`).

The canonical biconditional
(`continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational`) and the
Euler direction
(`isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic`) are proved
in `MathlibExt.NumberTheory.ContinuedFractions.EulerPeriodic`.

## Sources

* Amrik Singh Nimbran and Paul Levrie, "Patterns in Continued Fractions of
  Square Roots," Journal of Integer Sequences 26 (2023),
  <https://cs.uwaterloo.ca/journals/JIS/VOL26/Nimbran/nimbran14.tex>.
* The eventual-periodicity definition is lines 130–134; exact newline-terminated
  raw span SHA-256:
  `6d3b24948521d4d3fa03d6e17261c9442aa6cdf875126db573c9575a66623a7e`.
* The Euler–Lagrange statement is line 136; exact newline-terminated raw span
  SHA-256:
  `5be80578f3e620afa4d20050b29627a4c251e6ff852720806a9a42a0ff884b42`.
* Complete source file SHA-256:
  `08f38fd112c2dedb3802fe71799b670f6d2dbf5f49a89afdc0828156b8f56180`.
* Archive: `lagrange_periodic_cf_release_v2_D119163759`.
-/


namespace MetaMathlibExt

section

/-- The Möbius identity: `x = (P (n+1) ξ (n+1) + P n) / (Q (n+1) ξ (n+1) + Q n)`. -/
theorem cfMobius (x : ℝ) (hx : Irrational x) (n : ℕ) :
    x = ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
      / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
  induction n with
  | zero =>
    change x = ((cfP x 1 : ℝ) * cfXi x 1 + (cfP x 0 : ℝ))
      / ((cfQ x 1 : ℝ) * cfXi x 1 + (cfQ x 0 : ℝ))
    have hfx : Int.fract x ≠ 0 := by
      have h := fract_cfXi_ne x hx 0
      rwa [cfXi_zero] at h
    have hxi : cfXi x 1 = (Int.fract x)⁻¹ := cfXi_succ x 0
    rw [cfP_one, cfP_zero, cfQ_one, cfQ_zero, hxi]
    have h1 := Int.floor_add_fract x
    have hden : ((1 : ℤ) : ℝ) * (Int.fract x)⁻¹ + ((0 : ℤ) : ℝ) ≠ 0 := by
      have hne := inv_ne_zero hfx
      simpa using hne
    have hfinv : (Int.fract x)⁻¹ * Int.fract x = 1 := inv_mul_cancel₀ hfx
    rw [eq_div_iff hden]
    linear_combination hfinv - (Int.fract x)⁻¹ * h1
  | succ n ih =>
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfP_add_two x n, cfQ_add_two x n]
    have hgt : (1 : ℝ) < cfXi x (n + 2) := one_lt_cfXi_succ x hx (n + 1)
    have ht : cfXi x (n + 2) ≠ 0 := by linarith
    have hs := cfXi_eq_floor_add_inv x hx n
    have hts : cfXi x (n + 2) * cfXi x (n + 1)
        = cfXi x (n + 2) * ↑⌊cfXi x (n + 1)⌋ + 1 := by
      conv_lhs => rw [hs]
      rw [mul_add, mul_inv_cancel₀ ht]
    have hnum : ((⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n : ℤ) : ℝ)
          * cfXi x (n + 2) + (cfP x (n + 1) : ℝ)
        = cfXi x (n + 2)
          * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) := by
      push_cast
      linear_combination -((cfP x (n + 1) : ℝ)) * hts
    have hden : ((⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n : ℤ) : ℝ)
          * cfXi x (n + 2) + (cfQ x (n + 1) : ℝ)
        = cfXi x (n + 2)
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
      push_cast
      linear_combination -((cfQ x (n + 1) : ℝ)) * hts
    rw [hnum, hden, mul_div_mul_left _ _ ht]
    exact ih

/-- Approximation quality: `|Q (n+1) x - P (n+1)| = 1 / (Q (n+1) ξ (n+1) + Q n)`. -/
theorem cfApprox (x : ℝ) (hx : Irrational x) (n : ℕ) :
    |(cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)|
      = 1 / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
    ∧ |(cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)|
      ≤ 1 / (cfQ x (n + 1) : ℝ) := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hs : (1 : ℝ) < cfXi x (n + 1) := one_lt_cfXi_succ x hx n
  have hQ1R : (1 : ℝ) ≤ (cfQ x (n + 1) : ℝ) := by exact_mod_cast hQ1
  have hQ0R : (0 : ℝ) ≤ (cfQ x n : ℝ) := by exact_mod_cast hQ0
  have hden_pos : (0 : ℝ)
      < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) := by
    have hpos : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have hden_ne : (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) ≠ 0 :=
    ne_of_gt hden_pos
  have hmob := cfMobius x hx n
  have hdet := cfDet x n
  have heq : (cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)
      = -((cfP x (n + 1) : ℝ) * (cfQ x n : ℝ)
          - (cfP x n : ℝ) * (cfQ x (n + 1) : ℝ))
        / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
    have h2 : ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) :=
      div_mul_cancel₀ _ hden_ne
    rw [← hmob] at h2
    rw [eq_div_iff hden_ne]
    linear_combination (cfQ x (n + 1) : ℝ) * h2
  have habs : |(cfQ x (n + 1) : ℝ) * x - (cfP x (n + 1) : ℝ)|
      = 1 / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) := by
    rw [heq, abs_div, abs_of_pos hden_pos]
    congr 1
    have hdetR : (cfP x (n + 1) : ℝ) * (cfQ x n : ℝ)
          - (cfP x n : ℝ) * (cfQ x (n + 1) : ℝ) = (-1) ^ (n + 1) := by
      exact_mod_cast hdet
    rw [hdetR, abs_neg]
    simp
  refine ⟨habs, ?_⟩
  rw [habs]
  apply one_div_le_one_div_of_le (by linarith : (0 : ℝ) < cfQ x (n + 1))
  have hQs : (cfQ x (n + 1) : ℝ) * 1
      ≤ (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) :=
    mul_le_mul_of_nonneg_left (le_of_lt hs) (by linarith)
  rw [mul_one] at hQs
  linarith

end
end MetaMathlibExt
