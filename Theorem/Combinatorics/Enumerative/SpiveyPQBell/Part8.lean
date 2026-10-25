/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.SpiveyPQBell.Part7
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_BpolyScale_eval_one (p a : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    Polynomial.eval 1 (spivey_BpolyScale p S n a) =
      Polynomial.eval a (spivey_Bpoly p S n) := by
  rw [spivey_Bpoly_eval]
  simp [spivey_BpolyScale, Polynomial.eval_finsetSum]

lemma spivey_coe_BpolyScale (p a : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    ((spivey_BpolyScale p S n a : Polynomial ℝ) : PowerSeries ℝ) =
      ∑ k ∈ Finset.range (n + 1),
        ((p ^ Nat.choose k 2 * S n k) * a ^ k) • PowerSeries.X ^ k := by
  change Polynomial.coeToPowerSeries.ringHom (spivey_BpolyScale p S n a) = _
  rw [show spivey_BpolyScale p S n a = ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((p ^ Nat.choose k 2 * S n k) * a ^ k) * Polynomial.X ^ k by rfl,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_pow, Algebra.smul_def]

lemma spivey_rescale_monomial (a c : ℝ) (k : ℕ) :
    PowerSeries.rescale a (c • (PowerSeries.X : PowerSeries ℝ) ^ k) =
      (c * a ^ k) • PowerSeries.X ^ k := by
  apply PowerSeries.ext
  intro i
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul,
    PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
  by_cases hik : i = k
  · subst i
    simp
    ring
  · simp [hik]

lemma spivey_rescale_Bpoly (p a : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    PowerSeries.rescale a
        ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) =
      ((spivey_BpolyScale p S n a : Polynomial ℝ) : PowerSeries ℝ) := by
  rw [spivey_coe_Bpoly, map_sum, spivey_coe_BpolyScale]
  apply Finset.sum_congr rfl
  intro k _
  exact spivey_rescale_monomial a (p ^ Nat.choose k 2 * S n k) k

lemma spivey_Nop_pow_Bpoly_mul
    (p : ℝ) (S : ℕ → ℕ → ℝ) (n a : ℕ) (f : PowerSeries ℝ) :
    ((spivey_Nop p) ^ a)
        (((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) * f) =
      ((spivey_BpolyScale p S n (p ^ a) : Polynomial ℝ) : PowerSeries ℝ) *
        ((spivey_Nop p) ^ a) f := by
  rw [spivey_Nop_pow_apply, spivey_Nop_pow_apply, map_mul,
    spivey_rescale_Bpoly]

lemma spivey_basis_E
    (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (n k : ℕ) (hkn : k ≤ n) :
    spivey_basis p bracket n k (spivey_E p bracket) =
      p ^ Nat.choose k 2 •
        (PowerSeries.X ^ k * ((spivey_Nop p) ^ n) (spivey_E p bracket)) := by
  change (spivey_Xop ^ k)
    (((spivey_Nop p) ^ (n - k))
      (((spivey_Dop bracket) ^ k) (spivey_E p bracket))) = _
  rw [spivey_Dop_pow_E p bracket hbracket_ne, map_smul, map_smul,
    spivey_Xop_pow_apply]
  congr 1
  rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hkn]

lemma spivey_bell_action
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) (n : ℕ) :
    ((spivey_Xop * spivey_Dop bracket) ^ n) (spivey_E p bracket) =
      ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) *
        ((spivey_Nop p) ^ n) (spivey_E p bracket) := by
  have hexp := congrArg
    (fun T : Module.End ℝ (PowerSeries ℝ) => T (spivey_E p bracket))
    (spivey_stirling_expansion p q bracket S hbracket0 hbracketAdd
      hS0 hSsucc0 hSsucc n)
  rw [LinearMap.sum_apply] at hexp
  calc
    ((spivey_Xop * spivey_Dop bracket) ^ n) (spivey_E p bracket) =
        ∑ k ∈ Finset.range (n + 1),
          (S n k • spivey_basis p bracket n k) (spivey_E p bracket) := hexp
    _ = ∑ k ∈ Finset.range (n + 1),
          (p ^ Nat.choose k 2 * S n k) •
            (PowerSeries.X ^ k *
              ((spivey_Nop p) ^ n) (spivey_E p bracket)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by
        simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
      rw [LinearMap.smul_apply, spivey_basis_E p bracket hbracket_ne n k hkn,
        smul_smul]
      congr 1
      ring
    _ = ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) *
          ((spivey_Nop p) ^ n) (spivey_E p bracket) := by
      rw [spivey_coe_Bpoly, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_mul_assoc]

lemma spivey_middle_E
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k)
    (m n k j : ℕ) (hkm : k ≤ m) (hjn : j ≤ n) :
    ((spivey_Nop p) ^ (n - j) *
        (spivey_Xop * spivey_Dop bracket) ^ j *
        (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k)
        (spivey_E p bracket) =
      p ^ Nat.choose k 2 •
        (((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
            PowerSeries ℝ) *
          ((spivey_Nop p) ^ (n + m)) (spivey_E p bracket)) := by
  change ((spivey_Nop p) ^ (n - j))
    (((spivey_Xop * spivey_Dop bracket) ^ j)
      (((spivey_Nop p) ^ (m - k))
        (((spivey_Dop bracket) ^ k) (spivey_E p bracket)))) = _
  rw [spivey_Dop_pow_E p bracket hbracket_ne]
  simp only [map_smul]
  congr 1
  have hNm : ((spivey_Nop p) ^ (m - k))
      (((spivey_Nop p) ^ k) (spivey_E p bracket)) =
      ((spivey_Nop p) ^ m) (spivey_E p bracket) := by
    rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hkm]
  rw [hNm]
  have hcomm := (spivey_Nop_commute_XDop bracket hbracket0 p).pow_pow m j
  have hcomm_apply :
      ((spivey_Xop * spivey_Dop bracket) ^ j)
          (((spivey_Nop p) ^ m) (spivey_E p bracket)) =
        ((spivey_Nop p) ^ m)
          (((spivey_Xop * spivey_Dop bracket) ^ j) (spivey_E p bracket)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← hcomm.eq]
  rw [hcomm_apply, ← Module.End.mul_apply, ← pow_add,
    show n - j + m = n + m - j by omega,
    spivey_bell_action p q bracket S hbracket0 hbracketAdd hbracket_ne
      hS0 hSsucc0 hSsucc j,
    spivey_Nop_pow_Bpoly_mul]
  congr 1
  rw [← Module.End.mul_apply, ← pow_add,
    show n + m - j + j = n + m by omega]

lemma spivey_main_term_E
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k)
    (m n k j : ℕ) (hkm : k ≤ m) (hjn : j ≤ n) :
    (spivey_Xop ^ k * (spivey_Nop p) ^ (n - j) *
        (spivey_Xop * spivey_Dop bracket) ^ j *
        (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k)
        (spivey_E p bracket) =
      p ^ Nat.choose k 2 •
        ((PowerSeries.X ^ k *
            ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
              PowerSeries ℝ)) *
          ((spivey_Nop p) ^ (n + m)) (spivey_E p bracket)) := by
  change (spivey_Xop ^ k)
    (((spivey_Nop p) ^ (n - j) *
      (spivey_Xop * spivey_Dop bracket) ^ j *
      (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k)
      (spivey_E p bracket)) = _
  rw [spivey_middle_E p q bracket S hbracket0 hbracketAdd hbracket_ne
    hS0 hSsucc0 hSsucc m n k j hkm hjn, map_smul, spivey_Xop_pow_apply]
  congr 1
  ring

lemma spivey_expand_term_E
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k)
    (m n k : ℕ) (hkm : k ≤ m) :
    ((spivey_Xop * spivey_Dop bracket) ^ n * spivey_basis p bracket m k)
        (spivey_E p bracket) =
      ∑ j ∈ Finset.range (n + 1),
        (((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) *
          p ^ Nat.choose k 2) •
          ((PowerSeries.X ^ k *
              ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
                PowerSeries ℝ)) *
            ((spivey_Nop p) ^ (n + m)) (spivey_E p bracket)) := by
  unfold spivey_basis
  rw [show (spivey_Xop * spivey_Dop bracket) ^ n *
      (spivey_Xop ^ k * (spivey_Nop p) ^ (m - k) *
        (spivey_Dop bracket) ^ k) =
      (((spivey_Xop * spivey_Dop bracket) ^ n * spivey_Xop ^ k) *
        (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k) by noncomm_ring,
    spivey_push_Xop bracket hbracket0 p q hbracketAdd,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  have hdist :
      (∑ j ∈ Finset.range (n + 1),
          spivey_Xop ^ k *
            (((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
              ((spivey_Nop p) ^ (n - j) *
                (spivey_Xop * spivey_Dop bracket) ^ j)) *
            (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k) =
        ∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
            (spivey_Xop ^ k * (spivey_Nop p) ^ (n - j) *
              (spivey_Xop * spivey_Dop bracket) ^ j *
              (spivey_Nop p) ^ (m - k) * (spivey_Dop bracket) ^ k) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_smul_comm, smul_mul_assoc]
    congr 1
  rw [hdist, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj
  rw [LinearMap.smul_apply,
    spivey_main_term_E p q bracket S hbracket0 hbracketAdd hbracket_ne
      hS0 hSsucc0 hSsucc m n k j hkm hjn, smul_smul]

end MetaMathlibExt
