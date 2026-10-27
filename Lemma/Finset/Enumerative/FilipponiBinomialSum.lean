import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.FilipponiBinomialSum
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[pascal_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
private lemma pascal_shift (N t : ℕ) :
  Nat.choose (N + 2 - (t + 1)) (t + 1) =
    Nat.choose (N + 1 - (t + 1)) (t + 1) + Nat.choose (N + 1 - (t + 1)) t := by
  by_cases h : t ≤ N
  · have e1 : N + 2 - (t + 1) = (N - t) + 1 := by omega
    have e2 : N + 1 - (t + 1) = N - t := by omega
    rw [e1, e2, Nat.choose_succ_succ']
    ac_rfl
  · have z1 : N + 2 - (t + 1) = 0 := by omega
    have z2 : N + 1 - (t + 1) = 0 := by omega
    rw [z1, z2]
    have h1 : (0 : ℕ) < t + 1 := by omega
    have h2 : (0 : ℕ) < t := by omega
    simp [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[eshift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
private lemma eshift (N t : ℕ) :
  Nat.choose (N + 1 - (t + 1)) t = Nat.choose (N - t) t := by
  by_cases h : t ≤ N
  · have e : N + 1 - (t + 1) = N - t := by omega
    rw [e]
  · by_cases ht : t = 0
    · omega
    · have z1 : N + 1 - (t + 1) = 0 := by omega
      have z2 : N - t = 0 := by omega
      rw [z1, z2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fib_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
private lemma fib_step (N S : ℕ) :
  ∑ t ∈ Finset.range (S + 2), Nat.choose (N + 2 - t) t =
    (∑ t ∈ Finset.range (S + 1), Nat.choose (N - t) t) +
    (∑ t ∈ Finset.range (S + 2), Nat.choose (N + 1 - t) t) := by
  have c1 : S + 2 = (S + 1) + 1 := by omega
  rw [c1, Finset.sum_range_succ' (fun t => Nat.choose (N + 2 - t) t) (S + 1)]
  have c2 : S + 2 = (S + 1) + 1 := by omega
  rw [c2, Finset.sum_range_succ' (fun t => Nat.choose (N + 1 - t) t) (S + 1)]
  simp_rw [pascal_shift N, eshift N, Finset.sum_add_distrib]
  simp [Nat.choose_zero_right]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[filip_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
private lemma filip_aux : ∀ (h n k : ℕ),
  (∑ t ∈ Finset.range (k + h + 1), Nat.choose (n + 2 * h - t) t) =
  ∑ j ∈ Finset.range (h + 1), Nat.choose h j * ff n k j := by
  intro h
  refine Nat.rec (motive := fun h => ∀ (n k : ℕ),
    (∑ t ∈ Finset.range (k + h + 1), Nat.choose (n + 2 * h - t) t) =
    ∑ j ∈ Finset.range (h + 1), Nat.choose h j * ff n k j) ?_ ?_ h
  · intro n k
    simp [ff]
  · intro h ih n k
    have ih1 := ih n k
    have ih2 := ih (n + 1) (k + 1)
    have key := fib_step (n + 2 * h) (k + h)
    have eL : k + (h + 1) + 1 = (k + h) + 2 := by omega
    have eN : n + 2 * (h + 1) = (n + 2 * h) + 2 := by ring
    rw [eL, eN, key]
    rw [Finset.sum_range_succ' (fun j => Nat.choose (h + 1) j * ff n k j) (h + 1)]
    have hC0 : Nat.choose (h + 1) 0 = 1 := Nat.choose_zero_right _
    rw [hC0, one_mul]
    have hC : ∀ j : ℕ, Nat.choose (h + 1) (j + 1) =
      Nat.choose h j + Nat.choose h (j + 1) :=
      fun j => Nat.choose_succ_succ' h j
    simp_rw [hC, add_mul, Finset.sum_add_distrib]
    have hCh0 : Nat.choose h 0 = 1 := Nat.choose_zero_right h
    have hChh : Nat.choose h (h + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_succ_self h)
    have hR : (∑ j ∈ Finset.range (h + 1), Nat.choose h j * ff n k j) =
      ff n k 0 + (∑ j ∈ Finset.range (h + 1),
        Nat.choose h (j + 1) * ff n k (j + 1)) := by
      rw [Finset.sum_range_succ' (fun j => Nat.choose h j * ff n k j) h,
        Finset.sum_range_succ (fun j => Nat.choose h (j + 1) * ff n k (j + 1)) h,
        hCh0, hChh, one_mul, zero_mul, add_zero]
      ac_rfl
    have hFG : ∀ j : ℕ, ff n k (j + 1) =
      ∑ i ∈ Finset.range ((k + 1) + j + 1),
        Nat.choose ((n + 1) + j - i) i := by
      intro j
      have r1 : k + (j + 1) + 1 = (k + 1) + j + 1 := by omega
      have r2 : n + (j + 1) = (n + 1) + j := by omega
      simp only [ff, r1, r2]
    have b1 : (k + 1) + h + 1 = (k + h) + 2 := by omega
    have b2 : (n + 1) + 2 * h = ((n + 2 * h) + 1) := by ring
    rw [b1, b2] at ih2
    simp only [ff] at ih2
    simp_rw [← hFG] at ih2
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[filipponi_binomial_sum_formula_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
lemma filipponi_binomial_sum_formula_general
  {n h k : ℕ} :
-- imply
  let f : ℕ → ℕ → ℕ := by
-- proof
  have hbase := filip_aux h n k
  change (∑ t ∈ Finset.range (k + h + 1), Nat.choose (n + 2 * h - t) t) =
    ∑ j ∈ Finset.range (h + 1), Nat.choose h j *
      (∑ i ∈ Finset.range (k + j + 1), Nat.choose (n + j - i) i)
  exact hbase
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[filipponi_binomial_sum_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
lemma filipponi_binomial_sum_formula
  {n h k : ℕ}
-- given
  (hhn : h ≤ n)
  (hk : 2 * k ≤ n - h) :
-- imply
  let f : ℕ → ℕ → ℕ :=
-- proof
  filipponi_binomial_sum_formula_general n h k
end



-- created on 2026-10-20
-- updated on 2026-10-26
