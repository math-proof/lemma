/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import sympy.atlas.Dynamics.EventuallyPeriodicSequence
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
/-- Eventual periodicity of the continued fraction of `x`: the expansion does not
terminate, and the tail partial denominators `partDens` (which omits the head
coefficient `a₀`) are eventually periodic. Nontermination rules out a
vacuous `Option.none` tail. Source: Nimbran–Levrie lines 130–134. -/
def ContinuedFractionEventuallyPeriodic (x : ℝ) : Prop :=
  ¬ (GenContFract.of x).Terminates ∧
    IsEventuallyPeriodic (fun n => (GenContFract.of x).partDens.get? n)

/-- Real quadratic irrationality: `x` is integral over `ℚ` with minimal polynomial
of degree two. Degree two over `ℚ` captures real quadratic irrationality.
Source: Nimbran–Levrie line 136 (Euler–Lagrange statement). -/
def IsRealQuadraticIrrational (x : ℝ) : Prop :=
  IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree = 2

/-- Complete quotients of `x`: `cfXi x 0 = x`, `cfXi x (n+1) = (fract (cfXi x n))⁻¹`. -/
private noncomputable def cfXi (x : ℝ) : ℕ → ℝ
  | 0 => x
  | (n + 1) => (Int.fract (cfXi x n))⁻¹

private theorem cfXi_succ (x : ℝ) (n : ℕ) : cfXi x (n + 1) = (Int.fract (cfXi x n))⁻¹ := rfl

/-- Every complete quotient of an irrational is irrational. -/
private theorem irr_cfXi (x : ℝ) (hx : Irrational x) : ∀ n : ℕ, Irrational (cfXi x n)
  | 0 => by rwa [cfXi_zero]
  | (n + 1) => by rw [cfXi_succ]; exact (irr_fract _ (irr_cfXi x hx n)).inv

/-- Splitting a complete quotient into integer and fractional parts. -/
private theorem cfXi_eq_floor_add_inv (x : ℝ) (_hx : Irrational x) (n : ℕ) :
    cfXi x (n + 1) = ↑⌊cfXi x (n + 1)⌋ + (cfXi x (n + 2))⁻¹ := by
  have h2 : cfXi x (n + 2) = (Int.fract (cfXi x (n + 1)))⁻¹ := cfXi_succ x (n + 1)
  have h1 := Int.floor_add_fract (cfXi x (n + 1))
  rw [h2, inv_inv]
  exact h1.symm

/-- Numerator convergents: `P 0 = 1`, `P 1 = ⌊x⌋`, `P (n+2) = ⌊ξ (n+1)⌋ P (n+1) + P n`. -/
private noncomputable def cfP (x : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => ⌊x⌋
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n

/-- Denominator convergents: `Q 0 = 0`, `Q 1 = 1`, `Q (n+2) = ⌊ξ (n+1)⌋ Q (n+1) + Q n`. -/
private noncomputable def cfQ (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n

/-- The Möbius identity: `x = (P (n+1) ξ (n+1) + P n) / (Q (n+1) ξ (n+1) + Q n)`. -/
private theorem cfMobius (x : ℝ) (hx : Irrational x) (n : ℕ) :
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
private theorem cfApprox (x : ℝ) (hx : Irrational x) (n : ℕ) :
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

/-- Leading coefficient of the auxiliary quadratic at level `n`. -/
private noncomputable def triA (a b c : ℤ) (x : ℝ) (n : ℕ) : ℤ :=
  a * cfP x (n + 1) ^ 2 + b * cfP x (n + 1) * cfQ x (n + 1) + c * cfQ x (n + 1) ^ 2

/-- Constant coefficient of the auxiliary quadratic at level `n`. -/
private noncomputable def triC (a b c : ℤ) (x : ℝ) (n : ℕ) : ℤ :=
  a * cfP x n ^ 2 + b * cfP x n * cfQ x n + c * cfQ x n ^ 2

/-- Middle coefficient of the auxiliary quadratic at level `n`. -/
private noncomputable def triB (a b c : ℤ) (x : ℝ) (n : ℕ) : ℤ :=
  2 * a * cfP x (n + 1) * cfP x n
    + b * (cfP x (n + 1) * cfQ x n + cfP x n * cfQ x (n + 1))
    + 2 * c * cfQ x (n + 1) * cfQ x n

/-- Each complete quotient is a root of its auxiliary integer quadratic. -/
private theorem tri_root (x : ℝ) (hx : Irrational x) (a b c : ℤ) (n : ℕ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ((triA a b c x n : ℤ) : ℝ) * (cfXi x (n + 1)) ^ 2
      + ((triB a b c x n : ℤ) : ℝ) * (cfXi x (n + 1))
      + ((triC a b c x n : ℤ) : ℝ) = 0 := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ1R : (1 : ℝ) ≤ (cfQ x (n + 1) : ℝ) := by exact_mod_cast hQ1
  have hQ0R : (0 : ℝ) ≤ (cfQ x n : ℝ) := by exact_mod_cast hQ0
  have hs : (1 : ℝ) < cfXi x (n + 1) := one_lt_cfXi_succ x hx n
  have hden_ne : (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) :=
      mul_pos (by linarith) (by linarith)
    have hlt : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) := by
      linarith
    exact ne_of_gt hlt
  have hmob := cfMobius x hx n
  have h2 : x * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
      = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) := by
    have h3 : ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) :=
      div_mul_cancel₀ _ hden_ne
    rw [← hmob] at h3
    exact h3
  have e1 : ((triA a b c x n : ℤ) : ℝ) * (cfXi x (n + 1)) ^ 2
        + ((triB a b c x n : ℤ) : ℝ) * (cfXi x (n + 1))
        + ((triC a b c x n : ℤ) : ℝ)
      = (a : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) ^ 2
        + (b : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        + (c : ℝ) * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2 := by
    simp only [triA, triB, triC]
    push_cast
    ring
  have e2 : (a : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) ^ 2
        + (b : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        + (c : ℝ) * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2
      = ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2
        * ((a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ)) := by
    rw [← h2]
    ring
  rw [e1, e2, hquad, mul_zero]

/-- Uniform real bound on the leading coefficients. -/
private theorem triA_real_le (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) (n : ℕ) :
    |((triA a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ1R : (1 : ℝ) ≤ ((cfQ x (n + 1) : ℤ) : ℝ) := by exact_mod_cast hQ1
  have hQnn : (0 : ℝ) ≤ ((cfQ x (n + 1) : ℤ) : ℝ) := by linarith
  set Q' : ℝ := ((cfQ x (n + 1) : ℤ) : ℝ) with hQ'def
  set P' : ℝ := ((cfP x (n + 1) : ℤ) : ℝ) with hP'def
  set F : ℝ := Q' * x - P' with hFdef
  have hFle : |Q' * x - P'| ≤ 1 / Q' := by
    rw [hQ'def, hP'def]
    exact (cfApprox x hx n).2
  have hFleF : |F| ≤ 1 / Q' := by rw [hFdef]; exact hFle
  have hQne : Q' ≠ 0 := ne_of_gt (by linarith)
  have hFQ : |F| * Q' ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hFleF hQnn
    rwa [one_div_mul_cancel hQne] at h
  have hF1 : |F| ≤ 1 := by
    calc |F| = |F| * 1 := (mul_one _).symm
      _ ≤ |F| * Q' := mul_le_mul_of_nonneg_left hQ1R (abs_nonneg _)
      _ ≤ 1 := hFQ
  have hF2 : F ^ 2 ≤ 1 := by
    have h := mul_le_mul hF1 hF1 (abs_nonneg F) zero_le_one
    rw [one_mul, ← pow_two, sq_abs] at h
    exact h
  have hFproof : F = ((cfQ x (n + 1) : ℤ) : ℝ) * x - ((cfP x (n + 1) : ℤ) : ℝ) := by
    rw [hFdef, hQ'def, hP'def]
  have hform := triA_eq_form x a b c n hquad F hFproof
  rw [hform]
  calc |((a : ℝ)) * F ^ 2 - F * Q' * (2 * (a : ℝ) * x + (b : ℝ))|
      ≤ |((a : ℝ)) * F ^ 2| + |F * Q' * (2 * (a : ℝ) * x + (b : ℝ))| := by
        have h := abs_add_le ((a : ℝ) * F ^ 2)
          (-(F * Q' * (2 * (a : ℝ) * x + (b : ℝ))))
        rwa [← sub_eq_add_neg, abs_neg] at h
    _ ≤ |(a : ℝ)| * 1 + 1 * |2 * (a : ℝ) * x + (b : ℝ)| := by
        refine add_le_add ?_ ?_
        · simp only [abs_mul, abs_of_nonneg (sq_nonneg F)]
          exact mul_le_mul_of_nonneg_left hF2 (abs_nonneg _)
        · simp only [abs_mul, abs_of_nonneg hQnn]
          exact mul_le_mul_of_nonneg_right hFQ (abs_nonneg _)
    _ = |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by rw [mul_one, one_mul]

/-- The leading coefficients take finitely many values. -/
private theorem triA_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ M : ℕ, ∀ n : ℕ, (triA a b c x n).natAbs ≤ M := by
  refine ⟨⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊, fun n => ?_⟩
  have hA := triA_real_le x hx a b c hquad n
  have hM : |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triA a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    le_trans hA hM
  have g1 : triA a b c x n
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ)
      ≤ triA a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- Uniform real bound on the constant coefficients. -/
private theorem triC_real_le (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) (n : ℕ) :
    |((triC a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by
  cases n with
  | zero =>
    have hC0 : triC a b c x 0 = a := by simp [triC, cfP_zero, cfQ_zero]
    rw [hC0]
    exact le_add_of_nonneg_right (abs_nonneg _)
  | succ n =>
    rw [triC_succ]
    exact triA_real_le x hx a b c hquad n

/-- The constant coefficients take finitely many values. -/
private theorem triC_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ M : ℕ, ∀ n : ℕ, (triC a b c x n).natAbs ≤ M := by
  refine ⟨⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊, fun n => ?_⟩
  have hC := triC_real_le x hx a b c hquad n
  have hM : |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triC a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    le_trans hC hM
  have g1 : triC a b c x n
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ)
      ≤ triC a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- The middle coefficients take finitely many values. -/
private theorem triB_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ K : ℕ, ∀ n : ℕ, (triB a b c x n).natAbs ≤ K := by
  have hA : ∀ n, |((triA a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    fun n => triA_real_le x hx a b c hquad n
  have hC : ∀ n, |((triC a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    fun n => triC_real_le x hx a b c hquad n
  have hRnn : (0 : ℝ) ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
      + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
        * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊, fun n => ?_⟩
  have hBn := triB_sq x a b c n
  have hAn := hA n
  have hCn := hC n
  have hAC : ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
      ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
        * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
    calc ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
        ≤ |((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)| :=
          le_abs_self _
      _ = |((triA a b c x n : ℤ) : ℝ)| * |((triC a b c x n : ℤ) : ℝ)| :=
          abs_mul _ _
      _ ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
          mul_le_mul hAn hCn (abs_nonneg _) hRnn
  have hB2 : ((triB a b c x n : ℤ) : ℝ) ^ 2
      ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) := by
    have hDle : ((b ^ 2 - 4 * a * c : ℤ) : ℝ)
        ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)| := le_abs_self _
    rw [hBn]
    linear_combination hDle + 4 * hAC
  have hBb : |((triB a b c x n : ℤ) : ℝ)|
      ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 := by
    by_cases h1 : |((triB a b c x n : ℤ) : ℝ)| ≤ 1
    · calc |((triB a b c x n : ℤ) : ℝ)| ≤ 1 := h1
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 := by
            have h1' : (0 : ℝ) ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)| := abs_nonneg _
            have h2' : (0 : ℝ) ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
                * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
              mul_nonneg hRnn hRnn
            linarith
    · push Not at h1
      calc |((triB a b c x n : ℤ) : ℝ)| ≤ ((triB a b c x n : ℤ) : ℝ) ^ 2 := by
            calc |((triB a b c x n : ℤ) : ℝ)|
                = |((triB a b c x n : ℤ) : ℝ)| * 1 := (mul_one _).symm
              _ ≤ |((triB a b c x n : ℤ) : ℝ)|
                  * |((triB a b c x n : ℤ) : ℝ)| :=
                  mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
              _ = ((triB a b c x n : ℤ) : ℝ) ^ 2 := by rw [← pow_two, sq_abs]
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) := hB2
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 :=
            le_add_of_nonneg_right zero_le_one
  have hK : |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triB a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℝ) :=
    le_trans hBb hK
  have g1 : triB a b c x n
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℤ)
      ≤ triB a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- Each complete quotient determines the next via the floor. -/
private theorem cfXi_step (x : ℝ) (k : ℕ) :
    cfXi x (k + 2) = 1 / (cfXi x (k + 1) - ⌊cfXi x (k + 1)⌋) := by
  have hfr : cfXi x (k + 1) - ⌊cfXi x (k + 1)⌋
      = Int.fract (cfXi x (k + 1)) := by
    have h := Int.floor_add_fract (cfXi x (k + 1))
    linarith
  rw [hfr, cfXi_succ]
  exact (one_div _).symm

/-- Complete quotients commute with shifting past one step. -/
private theorem cfXi_shift (v : ℝ) (k : ℕ) :
    cfXi ((Int.fract v)⁻¹) k = cfXi v (k + 1) := by
  induction k with
  | zero => rw [cfXi_zero, cfXi_succ, cfXi_zero]
  | succ k ih => rw [cfXi_succ, cfXi_succ, ih]

/-- The `n`-th partial denominator is the head coefficient of `ξₙ`. -/
private theorem partDens_eq_head (x : ℝ) (n : ℕ) :
    (GenContFract.of x).partDens.get? n
      = (GenContFract.of (cfXi x n)).partDens.get? 0 := by
  revert x
  induction n with
  | zero => intro x; rw [cfXi_zero]
  | succ n ih =>
    intro v
    have e : cfXi ((Int.fract v)⁻¹) n = (Int.fract (cfXi v n))⁻¹ := by
      rw [cfXi_shift, cfXi_succ]
    rw [partDens_shift v n, cfXi_succ, ← e]
    exact ih ((Int.fract v)⁻¹)

/-- The auxiliary quadratic polynomial for a coefficient triple. -/
private noncomputable def triPoly (A B C : ℝ) : Polynomial ℝ :=
  Polynomial.C C + Polynomial.C B * Polynomial.X + Polynomial.C A * Polynomial.X ^ 2

/-- The finite box containing all auxiliary coefficient triples. -/
private def triBox (M K : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-((M : ℤ))) ((M : ℤ)) ×ˢ Finset.Icc (-((K : ℤ))) ((K : ℤ))
    ×ˢ Finset.Icc (-((M : ℤ))) ((M : ℤ))

/-- The finite set of all roots of auxiliary polynomials over the box. -/
private noncomputable def triU (M K : ℕ) : Set ℝ :=
  ⋃ t ∈ ↑((triBox M K).filter (fun t : ℤ × ℤ × ℤ => t.1 ≠ 0)),
    {y | (triPoly ((t.1 : ℤ) : ℝ) ((t.2.1 : ℤ) : ℝ) ((t.2.2 : ℤ) : ℝ)).IsRoot y}

/-- Every complete quotient past the head lies in the finite root set. -/
private theorem cfXi_mem_triU (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
    (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0)
    (M K : ℕ)
    (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
    (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
    (hC : ∀ n, (triC a b c x n).natAbs ≤ M)
    (n : ℕ) :
    cfXi x (n + 1) ∈ triU M K := by
  have hbox := triple_mem_box a b c x M K hA hB hC n
  have hAne := triA_ne x hx a b c n noroot
  have h1 : (triA a b c x n, (triB a b c x n, triC a b c x n))
      ∈ (triBox M K).filter (fun t : ℤ × ℤ × ℤ => t.1 ≠ 0) :=
    Finset.mem_filter.mpr ⟨hbox, hAne⟩
  have h2 : (triPoly ((triA a b c x n : ℤ) : ℝ) ((triB a b c x n : ℤ) : ℝ)
      ((triC a b c x n : ℤ) : ℝ)).IsRoot (cfXi x (n + 1)) := by
    change (triPoly ((triA a b c x n : ℤ) : ℝ) ((triB a b c x n : ℤ) : ℝ)
      ((triC a b c x n : ℤ) : ℝ)).eval (cfXi x (n + 1)) = 0
    rw [triPoly_eval]
    exact tri_root x hx a b c n hquad
  exact Set.mem_biUnion (Finset.mem_coe.mpr h1) h2

/-- Shift map on tail complete-quotient values. -/
private noncomputable def xiShift (x : ℝ) (y : ↥(Set.range (fun n => cfXi x (n + 1)))) :
    ↥(Set.range (fun n => cfXi x (n + 1))) :=
  ⟨1 / (y.1 - ⌊y.1⌋), by
    obtain ⟨k, hk⟩ := y.2
    refine ⟨k + 1, ?_⟩
    change cfXi x (k + 1 + 1) = 1 / (y.1 - ⌊y.1⌋)
    have e : k + 1 + 1 = k + 2 := by omega
    rw [e, ← hk]
    exact cfXi_step x k⟩

/-- The shift map sends each tail quotient to the next. -/
private theorem xiShift_orbit (x : ℝ) (n : ℕ) :
    (⟨cfXi x (n + 1 + 1), n + 1, rfl⟩ : ↥(Set.range (fun n => cfXi x (n + 1))))
      = xiShift x ⟨cfXi x (n + 1), n, rfl⟩ := by
  apply Subtype.ext
  change cfXi x (n + 1 + 1) = 1 / (cfXi x (n + 1) - ⌊cfXi x (n + 1)⌋)
  have e : n + 1 + 1 = n + 2 := by omega
  rw [e]
  exact cfXi_step x n

/-- The tail complete quotients form an eventually periodic sequence. -/
private theorem cfXi_eventually_periodic (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
    (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0)
    (M K : ℕ)
    (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
    (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
    (hC : ∀ n, (triC a b c x n).natAbs ≤ M) :
    IsEventuallyPeriodic (fun n => cfXi x (n + 1)) := by
  have hfin : (Set.range (fun n => cfXi x (n + 1))).Finite := by
    refine Set.Finite.subset (triU_finite M K) (fun y hy => ?_)
    obtain ⟨n, rfl⟩ := hy
    exact cfXi_mem_triU x hx a b c hquad noroot M K hA hB hC n
  have : Fintype ↥(Set.range (fun n => cfXi x (n + 1))) := hfin.fintype
  obtain ⟨p, n₀, hp, hper⟩ := IsEventuallyPeriodic.of_finite_orbit (xiShift x)
    (fun n : ℕ => ⟨cfXi x (n + 1), n, rfl⟩) (fun n => xiShift_orbit x n)
  refine IsEventuallyPeriodic.of_witness (n₀ := n₀) hp (fun n hn => ?_)
  exact congrArg Subtype.val (hper n hn)

/-- Lagrange direction of the Euler–Lagrange theorem: a real quadratic irrational
has an eventually periodic continued fraction. The canonical biconditional
(`continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational`) and the
Euler direction are proved in
`MathlibExt.NumberTheory.ContinuedFractions.EulerPeriodic`.
-/
theorem continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational
    (x : ℝ) (h : IsRealQuadraticIrrational x) :
    ContinuedFractionEventuallyPeriodic x := by
  obtain ⟨hint, hdeg⟩ := h
  obtain ⟨a, b, c, ha, heq, hnoroot⟩ := quad_int_of_minpoly x hint hdeg
  have hirr : Irrational x := quad_irrational x hint hdeg
  have hnonterm : ¬ (GenContFract.of x).Terminates := by
    rw [GenContFract.terminates_iff_rat]
    intro hmem
    obtain ⟨q, hq⟩ := hmem
    apply hnoroot q
    rw [← hq]
    exact heq
  obtain ⟨M1, hM1⟩ := triA_bound x hirr a b c heq
  obtain ⟨K, hK⟩ := triB_bound x hirr a b c heq
  obtain ⟨M2, hM2⟩ := triC_bound x hirr a b c heq
  have hA : ∀ n, (triA a b c x n).natAbs ≤ max M1 M2 :=
    fun n => le_trans (hM1 n) (le_max_left _ _)
  have hC : ∀ n, (triC a b c x n).natAbs ≤ max M1 M2 :=
    fun n => le_trans (hM2 n) (le_max_right _ _)
  obtain ⟨p, n₀, hp, hper⟩ := cfXi_eventually_periodic x hirr a b c heq hnoroot
    (max M1 M2) K hA hK hC
  have hxi : ∀ n, n₀ ≤ n → cfXi x (n + p + 1) = cfXi x (n + 1) :=
    fun n hn => hper n hn
  refine ⟨hnonterm, IsEventuallyPeriodic.of_witness (n₀ := n₀ + 1) hp
    (fun m hm => ?_)⟩
  rw [partDens_eq_head x (m + p), partDens_eq_head x m]
  have hxi' : cfXi x (m + p) = cfXi x m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have e : n + 1 + p = n + p + 1 := by omega
    rw [e]
    exact hxi n (by omega)
  rw [hxi']

end
end MetaMathlibExt
