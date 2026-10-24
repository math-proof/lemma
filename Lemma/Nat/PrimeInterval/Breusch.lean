import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeInterval.Breusch
open MathlibExt.NumberTheory.BreuschWanted
open Internal


namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[chain_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma chain_prime
  :
-- imply
  ∀ p ∈ chain, p.Prime := by
-- proof
  intro p hp
  fin_cases hp <;> norm_num

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[chain_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma chain_sorted
  :
-- imply
  chain.Pairwise (· < ·) := by
-- proof
decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[chain_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma chain_ratio
  :
-- imply
  ∀ pr ∈ chain.zip chain.tail, 8 * pr.2 < 9 * pr.1 := by
-- proof
  decide

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[chain_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma chain_getLast
  :
-- imply
  chain.getLast (by decide : chain ≠ []) = 9820997 :=
-- proof
  rfl

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[bracket](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma bracket
  {X : ℝ} :
-- imply
  ∀ (l : List ℕ) (prev : ℕ), List.Pairwise (· < ·) (prev :: l) → (prev:ℝ) ≤ X → ∀ (hne : prev :: l ≠ []), (X:ℝ) < ((((prev :: l).getLast hne : ℕ)):ℝ) → ∃ (l1 : List ℕ) (a b : ℕ) (l2 : List ℕ), prev :: l = l1 ++ [a, b] ++ l2 ∧ (a:ℝ) ≤ X ∧ (X:ℝ) < (b:ℝ) := by
-- proof
  intro l
  induction l with
  | nil =>
    intro prev hs hlo hne hhi
    rw [List.getLast_singleton] at hhi
    linarith [hlo, hhi]
  | cons q qs ih =>
    intro prev hs hlo hne hhi
    have hsq : List.Pairwise (· < ·) (q :: qs) := (List.pairwise_cons.mp hs).2
    have hne2 : q :: qs ≠ [] := by simp
    have hget : (prev :: q :: qs).getLast hne = (q :: qs).getLast hne2 :=
      List.getLast_cons hne2
    by_cases hXq : (X:ℝ) < (q:ℝ)
    · exact ⟨[], prev, q, qs, by simp, hlo, hXq⟩
    · have hXq' : (q:ℝ) ≤ X := le_of_not_gt hXq
      obtain ⟨l1, a, b, l2, heq, haX, hXb⟩ :=
        ih q hsq hXq' hne2 (by rwa [hget] at hhi)
      exact ⟨prev :: l1, a, b, l2, by
        rw [show (prev :: l1) ++ [a, b] ++ l2 = prev :: (l1 ++ [a, b] ++ l2) by simp,
          ← heq], haX, hXb⟩

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[zip_cons_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma zip_cons_mem
  {R : List ℕ}
  {d a b : ℕ}
-- given
  (h : (a, b) ∈ R.zip R.tail) :
-- imply
  (a, b) ∈ (d :: R).zip (d :: R).tail := by
-- proof
  have etail : (d :: R).tail = R := rfl
  rw [etail]
  cases R with
  | nil => simp at h
  | cons r0 R' =>
    have etail2 : (r0 :: R').tail = R' := rfl
    rw [etail2] at h
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ h

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[zip_mem_of_consec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma zip_mem_of_consec
  {l : List ℕ}
  {a b : ℕ}
  {l1 l2 : List ℕ}
-- given
  (h : l = l1 ++ [a, b] ++ l2) :
-- imply
  (a, b) ∈ l.zip l.tail := by
-- proof
  subst h
  induction l1 with
  | nil =>
    have e : (([] : List ℕ) ++ [a, b] ++ l2) = a :: b :: l2 := rfl
    rw [e]
    have etail : (a :: b :: l2).tail = b :: l2 := rfl
    rw [etail, List.zip_cons_cons]
    exact List.mem_cons.mpr (Or.inl rfl)
  | cons c cs ih =>
    have e : ((c :: cs) ++ [a, b] ++ l2) = c :: (cs ++ [a, b] ++ l2) := rfl
    rw [e]
    exact zip_cons_mem ih

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[chain_cover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma chain_cover
  {X : ℝ}
-- given
  (hlo : (53 : ℝ) ≤ X)
  (hhi : X < (9820997 : ℝ)) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
-- proof
  have hchain : chain = 53 :: chain.tail := rfl
  have hsorted : List.Pairwise (· < ·) (53 :: chain.tail) := by
    rw [← hchain]; exact chain_sorted
  have hne53 : 53 :: chain.tail ≠ [] := by simp
  have hlast : (53 :: chain.tail).getLast hne53 = 9820997 := rfl
  have hhi2 : X < (((9820997 : ℕ)) : ℝ) := by exact_mod_cast hhi
  obtain ⟨l1, a, b, l2, heq, haX, hXb⟩ :=
    bracket X chain.tail 53 hsorted hlo hne53 (by rwa [← hlast] at hhi2)
  have heq' : chain = l1 ++ [a, b] ++ l2 := by rw [hchain]; exact heq
  have hmem : (a, b) ∈ chain.zip chain.tail := zip_mem_of_consec heq'
  have hratio := chain_ratio (a, b) hmem
  have hb : b ∈ chain := by rw [heq']; simp
  have hprime := chain_prime b hb
  refine ⟨b, hprime, hXb, ?_⟩
  have hratioR : (8:ℝ)*b < 9*a := by exact_mod_cast hratio
  have haR : (a : ℝ) ≤ X := haX
  linarith [hratioR, haR]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[overlap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma overlap
  {X : ℝ}
-- given
  (hX : (5600 * 4762 / 3 : ℝ) ≤ X) :
-- imply
  ∃ n : ℕ, 4762 ≤ n ∧ (5600 : ℝ) * n / 3 ≤ X ∧ X ≤ (1890 : ℝ) * n := by
-- proof
  set n := ⌊3 * X / 5600⌋₊ with hn
  have hXnn : (0 : ℝ) ≤ 3 * X / 5600 := by linarith [hX]
  refine ⟨n, ?_, ?_, ?_⟩
  · apply Nat.le_floor
    push_cast
    linarith [hX]
  · have hle : (n : ℝ) ≤ 3 * X / 5600 := Nat.floor_le hXnn
    linarith [hle]
  · have hlt := Nat.lt_floor_add_one (3 * X / 5600)
    linarith [hlt, hX]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[main_contra](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma main_contra
  {n : ℕ}
-- given
  (hn : 4762 ≤ n)
  (_hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False)
  (hupper : upper_ineq n) :
-- imply
  False := by
-- proof
  unfold upper_ineq at hupper
  have hn1 : 1 ≤ n := by omega
  have hlower := logF9_lower n hn1
  have hgap := gap_pos n hn
  have hmargin := T03c_eqmain_margin
  have h34 : Real.log (34/10:ℝ) = Real.log 3.4 := by congr 1; norm_num
  rw [h34] at hmargin
  have hcast : (((2100 * n : ℕ)) : ℝ) = (2100 : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hcast] at hlower
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmargin_n := mul_lt_mul_of_pos_right hmargin hn0
  linarith [hlower, hupper, hgap, hmargin_n]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[analytic_at_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma analytic_at_X
  {X : ℝ}
-- given
  (hX : (5600 * 4762 / 3 : ℝ) ≤ X)
  (hU : ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → upper_ineq n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
-- proof
  obtain ⟨n, hn0, hnlo, hnhi⟩ := overlap X hX
  by_contra hcon
  have hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False := by
    intro p hp hlo hhi
    apply hcon
    have h1 : (X : ℝ) < (p : ℝ) := by
      have h : ((1890 * n : ℕ):ℝ) < (p : ℝ) := by exact_mod_cast hlo
      have hcast : ((1890 * n : ℕ):ℝ) = (1890 : ℝ) * (n : ℝ) := by push_cast; ring
      rw [hcast] at h
      linarith [hnhi, h]
    have h2 : (p : ℝ) < (9 / 8 : ℝ) * X := by
      -- 2100 * n is composite, so the prime p is strictly below it.
      have hne : p ≠ 2100 * n := by
        intro heq
        have h2dvd : 2 ∣ p := by rw [heq]; exact ⟨1050 * n, by ring⟩
        have h2lt : 2 < p := by
          have hlo' := hlo
          have hn1 : 1 ≤ n := by omega
          omega
        have hdis := hp.eq_one_or_self_of_dvd 2 h2dvd
        omega
      have hhiR : (p : ℝ) < ((2100 * n : ℕ):ℝ) :=
        by exact_mod_cast (lt_of_le_of_ne hhi hne)
      have hcast : ((2100 * n : ℕ):ℝ) = (2100 : ℝ) * (n : ℝ) := by push_cast; ring
      rw [hcast] at hhiR
      have hle : (2100 : ℝ) * (n : ℝ) ≤ (9 / 8 : ℝ) * X := by linarith [hnlo]
      linarith [hhiR, hle]
    exact ⟨p, hp, h1, h2⟩
  exact main_contra n hn0 hA (hU n (by omega) hA)

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[breusch_prime_interval_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma breusch_prime_interval_of_upper
  {x : ℝ}
-- given
  (hx : 48 ≤ x)
  (hU : ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → upper_ineq n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (x : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
-- proof
  by_cases hX0 : x < (5600 * 4762 / 3 : ℝ)
  · by_cases h53 : x < 53
    · refine ⟨53, by norm_num, h53, ?_⟩
      linarith [hx]
    · have h53' : (53 : ℝ) ≤ x := le_of_not_gt h53
      have hlast : x < (9820997 : ℝ) := by
        have hle : (5600 * 4762 / 3 : ℝ) ≤ (9820997 : ℝ) := by norm_num
        linarith [hX0, hle]
      exact chain_cover x h53' hlast
  · have hX0' : (5600 * 4762 / 3 : ℝ) ≤ x := le_of_not_gt hX0
    exact analytic_at_X x hX0' hU

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted

/--
[breusch_prime_interval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
lemma breusch_prime_interval
  :
-- imply
  ∀ x : ℝ, 48 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
-- proof
  intro x hx
  exact Internal.breusch_prime_interval_of_upper x hx
    (fun n hn hA => Internal.logF9_upper n hn hA)

end MathlibExt.NumberTheory.BreuschWanted


-- created on 2026-10-20
-- updated on 2026-10-23
