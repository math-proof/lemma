import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[recip_choose_split](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StaverReciprocalBinomialSum.lean)
-/
@[path]
`Nat.choose (n + 1)` at `k` and `k + 1` through `Nat.choose_mul_succ_eq` and
`Nat.choose_succ_right_eq` exhibits both children as multiples of
`Nat.choose n k`; since the two cofactors `(n + 1 - k)` and `(k + 1)` add up
to `n + 2`, clearing denominators gives the stated reciprocal identity. -/
private lemma recip_choose_split (n k : ℕ) (hk : k ≤ n) :
  ((Nat.choose n k : Rat))⁻¹
    = (((n : Rat) + 1) / ((n : Rat) + 2))
      * (((Nat.choose (n + 1) k : Rat))⁻¹
        + ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹) := by
  have hE1 : (Nat.choose n k : Rat) * ((n : Rat) + 1)
    = (Nat.choose (n + 1) k : Rat) * ((n + 1 - k : ℕ) : Rat) := by
    have hR := congrArg (Nat.cast : ℕ → Rat) (Nat.choose_mul_succ_eq n k)
    simpa using hR
  have hE2 : (Nat.choose (n + 1) (k + 1) : Rat) * ((k : Rat) + 1)
    = ((n : Rat) + 1) * (Nat.choose n k : Rat) := by
    have h : Nat.choose (n + 1) (k + 1) * (k + 1)
      = (n + 1) * Nat.choose n k :=
      calc Nat.choose (n + 1) (k + 1) * (k + 1)
        = Nat.choose (n + 1) k * (n + 1 - k) :=
          Nat.choose_succ_right_eq (n + 1) k
        _ = Nat.choose n k * (n + 1) := (Nat.choose_mul_succ_eq n k).symm
        _ = (n + 1) * Nat.choose n k := Nat.mul_comm _ _
    have hR := congrArg (Nat.cast : ℕ → Rat) h
    simpa using hR
  have hUV : ((n + 1 - k : ℕ) : Rat) + ((k : Rat) + 1) = (n : Rat) + 2 := by
    have h : (n + 1 - k) + (k + 1) = n + 2 := by omega
    have hR := congrArg (Nat.cast : ℕ → Rat) h
    simpa using hR
  have : (Nat.choose n k : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have : (Nat.choose (n + 1) k : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_succ_of_le hk)).ne'
  have : (Nat.choose (n + 1) (k + 1) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.succ_le_succ hk)).ne'
  have : ((n : Rat) + 2) ≠ 0 := by
    have h : ((n + 2 : ℕ) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  field_simp
  linear_combination (-((Nat.choose (n + 1) (k + 1) : Rat))) * hE1
    + ((Nat.choose (n + 1) k : Rat)) * hE2
    - (((Nat.choose (n + 1) k : Rat))
      * ((Nat.choose (n + 1) (k + 1) : Rat))) * hUV

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lhs_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StaverReciprocalBinomialSum.lean)
-/
@[path]
`n`-sum through two shifted copies of the `(n + 1)`-sum, each equal to that
sum minus its endpoint value `1`, and solving for the `(n + 1)`-sum gives the
recurrence. -/
private lemma lhs_recurrence (n : ℕ) :
  (Finset.range (n + 1 + 1)).sum (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
    = 1 + ((((n : Rat) + 2) / (2 * ((n : Rat) + 1)))
      * ((Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹))) := by
  have hsum : (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹)
    = (((n : Rat) + 1) / ((n : Rat) + 2))
      * ((Finset.range (n + 1)).sum
        (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹
          + ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    exact recip_choose_split n k hkn
  have hfirst : (Finset.range (n + 1)).sum
    (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
    = (Finset.range (n + 1 + 1)).sum
      (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) - 1 := by
    have hsucc : (Finset.range (n + 1 + 1)).sum
      (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
      = (Finset.range (n + 1)).sum (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
        + ((Nat.choose (n + 1) (n + 1) : Rat))⁻¹ :=
      Finset.sum_range_succ (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) (n + 1)
    have hlast : ((Nat.choose (n + 1) (n + 1) : Rat))⁻¹ = 1 := by
      rw [Nat.choose_self]
      simp
    rw [hlast] at hsucc
    linear_combination -1 * hsucc
  have hsecond : (Finset.range (n + 1)).sum
    (fun k => ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)
    = (Finset.range (n + 1 + 1)).sum
      (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) - 1 := by
    have hsucc : (Finset.range (n + 1 + 1)).sum
      (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
      = (Finset.range (n + 1)).sum
        (fun k => ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)
        + ((Nat.choose (n + 1) 0 : Rat))⁻¹ :=
      Finset.sum_range_succ' (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) (n + 1)
    have hfirst0 : ((Nat.choose (n + 1) 0 : Rat))⁻¹ = 1 := by
      rw [Nat.choose_zero_right]
      simp
    rw [hfirst0] at hsucc
    linear_combination -1 * hsucc
  have hsplit : (Finset.range (n + 1)).sum
    (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹
      + ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)
    = (Finset.range (n + 1)).sum (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
      + (Finset.range (n + 1)).sum
        (fun k => ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹) :=
    Finset.sum_add_distrib
  have : ((n : Rat) + 1) ≠ 0 := by
    have h : ((n + 1 : ℕ) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : ((n : Rat) + 2) ≠ 0 := by
    have h : ((n + 2 : ℕ) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : (2 : Rat) ≠ 0 := by decide
  have heq : (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹)
    = (((n : Rat) + 1) / ((n : Rat) + 2))
      * (2 * ((Finset.range (n + 1 + 1)).sum
        (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)) - 2) := by
    rw [hsum, hsplit, hfirst, hsecond]
    ring
  field_simp at heq ⊢
  linear_combination -1 * heq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rhs_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StaverReciprocalBinomialSum.lean)
-/
@[path]
`(n + 1)`-side through the `n`-side, and the new top term cancels the leading
prefactor to leave exactly `1` plus the expected multiple. -/
private lemma rhs_recurrence (n : ℕ) :
  (((n : Rat) + 2) / (2 : Rat) ^ (n + 1 + 1))
    * ((Finset.Icc 1 (n + 1 + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat)))
    = 1 + ((((n : Rat) + 2) / (2 * ((n : Rat) + 1)))
      * ((((n : Rat) + 1) / (2 : Rat) ^ (n + 1))
        * ((Finset.Icc 1 (n + 1)).sum
          (fun k => (2 : Rat) ^ k / (k : Rat))))) := by
  have hU : (Finset.Icc 1 (n + 1 + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat))
    = (Finset.Icc 1 (n + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat))
      + (2 : Rat) ^ (n + 1 + 1) / ((((n + 1 + 1 : ℕ))) : Rat) :=
    Finset.sum_Icc_succ_top (by omega) (fun k => (2 : Rat) ^ k / (k : Rat))
  have hcast : ((((n + 1 + 1 : ℕ))) : Rat) = (n : Rat) + 2 := by
    have h : (n + 1 + 1) = n + 2 := by omega
    have hR := congrArg (Nat.cast : ℕ → Rat) h
    simpa using hR
  have hpow_eq : (2 : Rat) ^ (n + 1 + 1) = 2 * (2 : Rat) ^ (n + 1) := by
    rw [pow_succ]
    ring
  have : ((n : Rat) + 1) ≠ 0 := by
    have h : ((((n + 1 : ℕ))) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : ((n : Rat) + 2) ≠ 0 := by
    have h : ((((n + 2 : ℕ))) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : (2 : Rat) ≠ 0 := by decide
  have : (2 : Rat) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by decide)
  rw [hU, hcast, hpow_eq]
  field_simp
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[staver_reciprocal_binomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StaverReciprocalBinomialSum.lean)
-/
@[path]
lemma staver_reciprocal_binomial_sum
  {n : Nat} :
-- imply
  (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹) =
    ((n + 1 : Rat) / (2 : Rat) ^ (n + 1)) *
    (Finset.Icc 1 (n + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat)) := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    have hL := lhs_recurrence n
    have hR := rhs_recurrence n
    simp only [Nat.cast_succ] at ih ⊢
    have h2 : ((n : Rat) + 1) + 1 = (n : Rat) + 2 := by ring
    rw [h2] at ⊢
    rw [hL, hR, ih]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
