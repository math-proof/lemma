import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Recurrences.HonsbergerFibonacciP
open MetaMathlibExt


namespace MetaMathlibExt

/--
[fibonacciP_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
lemma fibonacciP_zero
  {p : ℕ} :
-- imply
  fibonacciP p 0 = 0 := by
-- proof
  rw [fibonacciP]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibonacciP_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
lemma fibonacciP_eq_one
  {p r : ℕ}
-- given
  (hr : 1 ≤ r)
  (hrp : r ≤ p) :
-- imply
  fibonacciP p r = 1 := by
-- proof
  cases r with
  | zero => omega
  | succ r => simp [fibonacciP, hrp]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibonacciP_rec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
lemma fibonacciP_rec
  {p r : ℕ}
-- given
  (hpr : p < r) :
-- imply
  fibonacciP p r = fibonacciP p (r - 1) + fibonacciP p (r - p - 1) := by
-- proof
  cases r with
  | zero => omega
  | succ r =>
    have hnot : ¬r + 1 ≤ p := by omega
    have hsub : r + 1 - p - 1 = r - p := by omega
    simp [fibonacciP, hnot, hsub]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibonacciP_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
lemma fibonacciP_one
  {n : ℕ} :
-- imply
  fibonacciP 1 n = Nat.fib n := by
-- proof
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp [fibonacciP]
      | succ n =>
        change fibonacciP 1 (n + 2) = Nat.fib (n + 2)
        rw [fibonacciP_rec 1 (n + 2) (by omega)]
        rw [show n + 2 - 1 = n + 1 by omega]
        rw [show n + 1 - 1 = n by omega]
        rw [ih (n + 1) (by omega), ih n (by omega), Nat.fib_add_two]
        omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[honsberger_uniform_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma honsberger_uniform_recurrence
  (p : ℕ) (f : ℕ → ℕ)
  (hzero : f 0 = 0)
  (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
  (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1))
  (r : ℕ) (hr : 1 ≤ r) :
  f (r + 1) = f r + f (r - p) := by
  by_cases hle : r + 1 ≤ p
  · have hrp : r ≤ p := by omega
    have hsub : r - p = 0 := by omega
    rw [hone (r + 1) (by omega) hle, hone r hr hrp, hsub, hzero]
  · have hgt : p < r + 1 := by omega
    rw [hrec (r + 1) hgt]
    have hpred : r + 1 - 1 = r := by omega
    have hsub : r + 1 - p - 1 = r - p := by omega
    rw [hpred, hsub]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[honsberger_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma honsberger_telescope
  (p n k : ℕ) (f : ℕ → ℕ)
  (hzero : f 0 = 0)
  (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
  (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1)) :
  f (n + 2) + ∑ j ∈ Finset.range k, f (n + j + 2 - p) = f (n + k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    rw [← honsberger_uniform_recurrence p f hzero hone hrec (n + k + 2) (by omega)]
    congr 1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[honsberger_base](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma honsberger_base
  (p m n : ℕ) (f : ℕ → ℕ) (hp : 0 < p)
  (hzero : f 0 = 0)
  (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
  (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1))
  (hm : m ≤ p) :
  f (m + 1) * f (n + 2) +
    ∑ j ∈ Finset.range p, f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
    f (m + n + 2) := by
  have hfm1 : f (m + 1) = 1 := by
    by_cases hmp : m < p
    · exact hone (m + 1) (by omega) (by omega)
    · have hmp_eq : m = p := by omega
      subst m
      rw [honsberger_uniform_recurrence p f hzero hone hrec p hp]
      rw [hone p hp le_rfl, Nat.sub_self, hzero]
  have hsubset : Finset.range m ⊆ Finset.range p := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hsum :
    (∑ j ∈ Finset.range p,
      f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) =
      ∑ j ∈ Finset.range m, f (n + j + 2 - p) := by
    calc
      (∑ j ∈ Finset.range p,
        f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) =
        ∑ j ∈ Finset.range m,
          f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) := by
          symm
          apply Finset.sum_subset hsubset
          intro j hjp hjm
          simp only [Finset.mem_range] at hjp hjm
          have hidx : m + 1 - (j + 1) = 0 := by omega
          rw [hidx, hzero, zero_mul]
      _ = ∑ j ∈ Finset.range m, f (n + j + 2 - p) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hfirst : m + 1 - (j + 1) = m - j := by omega
        have hpos : 1 ≤ m - j := by omega
        have hle : m - j ≤ p := by omega
        have hsecond : n + (j + 1) + 1 - p = n + j + 2 - p := by omega
        rw [hfirst, hone (m - j) hpos hle, one_mul, hsecond]
  rw [hfm1, one_mul, hsum]
  rw [honsberger_telescope p n m f hzero hone hrec]
  congr 1
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[honsberger_induction_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma honsberger_induction_step
  (p m n : ℕ) (f : ℕ → ℕ)
  (hzero : f 0 = 0)
  (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
  (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1))
  (hpm : p < m)
  (hprev :
    f ((m - 1) + 1) * f (n + 2) +
      ∑ j ∈ Finset.range p,
        f ((m - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
      f ((m - 1) + n + 2))
  (hback :
    f ((m - p - 1) + 1) * f (n + 2) +
      ∑ j ∈ Finset.range p,
        f ((m - p - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
      f ((m - p - 1) + n + 2)) :
  f (m + 1) * f (n + 2) +
    ∑ j ∈ Finset.range p,
      f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
    f (m + n + 2) := by
  have hfm := honsberger_uniform_recurrence p f hzero hone hrec m (by omega)
  have hsum :
    (∑ j ∈ Finset.range p,
      f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) =
      (∑ j ∈ Finset.range p,
        f ((m - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p)) +
      ∑ j ∈ Finset.range p,
        f ((m - p - 1) + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hr : 1 ≤ m - 1 - j := by omega
    have hleft : m + 1 - (j + 1) = (m - 1 - j) + 1 := by omega
    have hprev_index : (m - 1) + 1 - (j + 1) = m - 1 - j := by omega
    have hback_index : (m - p - 1) + 1 - (j + 1) = m - 1 - j - p := by omega
    rw [hleft, honsberger_uniform_recurrence p f hzero hone hrec (m - 1 - j) hr]
    rw [add_mul, hprev_index, hback_index]
  have hm_prev_index : m = (m - 1) + 1 := by omega
  have hm_back_index : m - p = (m - p - 1) + 1 := by omega
  have hfm_prev : f m = f ((m - 1) + 1) := congrArg f hm_prev_index
  have hfm_back : f (m - p) = f ((m - p - 1) + 1) := congrArg f hm_back_index
  have hprev' := hprev
  have hback' := hback
  have hprev_result : (m - 1) + n + 2 = m + n + 1 := by omega
  have hback_result : (m - p - 1) + n + 2 = m + n + 1 - p := by omega
  rw [hprev_result] at hprev'
  rw [hback_result] at hback'
  have hfinal :=
    honsberger_uniform_recurrence p f hzero hone hrec (m + n + 1) (by omega)
  have hfinal_index : m + n + 1 + 1 = m + n + 2 := by omega
  rw [hfinal_index] at hfinal
  rw [hfm, hsum, add_mul, hfm_prev, hfm_back]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[honsberger_generic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma honsberger_generic
  (p m n : ℕ) (f : ℕ → ℕ) (hp : 0 < p)
  (hzero : f 0 = 0)
  (hone : ∀ r, 1 ≤ r → r ≤ p → f r = 1)
  (hrec : ∀ r, p < r → f r = f (r - 1) + f (r - p - 1)) :
  f (m + 1) * f (n + 2) +
    ∑ j ∈ Finset.range p,
      f (m + 1 - (j + 1)) * f (n + (j + 1) + 1 - p) =
    f (m + n + 2) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ p
    · exact honsberger_base p m n f hp hzero hone hrec hm
    · exact honsberger_induction_step p m n f hzero hone hrec (by omega)
      (ih (m - 1) (by omega)) (ih (m - p - 1) (by omega))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[honsberger_fibonacciP](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
lemma honsberger_fibonacciP
  {p m n : ℕ}
-- given
  (hp : 0 < p)
  (hm_pos : 0 < m)
  (hn_pos : 0 < n)
  (hm : p ≤ m + 1)
  (hn : p ≤ n + 2) :
-- imply
  fibonacciP p 0 = 0 →
    (∀ r, 1 ≤ r → r ≤ p → fibonacciP p r = 1) →
    (∀ r, p < r →
    fibonacciP p r =
    fibonacciP p (r - 1) + fibonacciP p (r - p - 1)) →
    fibonacciP p (m + 1) * fibonacciP p (n + 2) +
    ∑ j ∈ Finset.range p,
    fibonacciP p (m + 1 - (j + 1)) *
    fibonacciP p (n + (j + 1) + 1 - p) =
    fibonacciP p (m + n + 2) := by
-- proof
  intro hzero hone hrec
  exact honsberger_generic p m n (fibonacciP p) hp hzero hone hrec

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
