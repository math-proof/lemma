import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.DirectedCycles.Part2
open Real Finset DirectedCycles DirectedCycles.DirectedWalk


namespace DirectedCycles.DirectedWalk

/--
[length_cast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma length_cast
  {G : Digraph V}
  {u v u' v' : V}
  {p : DirectedWalk G u v}
-- given
  (hu : u = u')
  (hv : v = v') :
-- imply
  (p.cast hu hv).length = p.length := by
-- proof
  subst hu; subst hv; rfl

end DirectedCycles.DirectedWalk

namespace DirectedCycles

/--
[consWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma consWalk_length
  {G : Digraph V}
  {seq : ℕ → V}
  {m : ℕ}
-- given
  (hadj : ∀ n : ℕ, G.Adj (seq n) (seq (n + 1))) :
-- imply
  (consWalk G seq hadj m).length = m := by
-- proof
  induction m generalizing seq hadj with
  | zero => rfl
  | succ m ih => simp [consWalk, DirectedWalk.length, ih]

end DirectedCycles

namespace DirectedCycles

/--
[mem_consWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma mem_consWalk_support
  {G : Digraph V}
  {seq : ℕ → V}
  {m : ℕ}
  {v : V}
-- given
  (hadj : ∀ n : ℕ, G.Adj (seq n) (seq (n + 1))) :
-- imply
  v ∈ (consWalk G seq hadj m).support ↔ ∃ i, i ≤ m ∧ v = seq i := by
-- proof
  induction m generalizing seq hadj with
  | zero =>
    simp only [consWalk, DirectedWalk.support, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, le_refl 0, h⟩
    · rintro ⟨i, hi, rfl⟩; have := Nat.le_zero.mp hi; subst this; rfl
  | succ m ih =>
    simp only [consWalk, DirectedWalk.support, List.mem_cons]
    constructor
    · rintro (rfl | hmem)
      · exact ⟨0, Nat.zero_le _, rfl⟩
      · rw [ih] at hmem; obtain ⟨i, hi, rfl⟩ := hmem; exact ⟨i + 1, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => left; rfl
      | succ i => right; rw [ih]; exact ⟨i, by omega, rfl⟩

end DirectedCycles

namespace DirectedCycles

/--
[consWalk_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma consWalk_support_nodup
  {G : Digraph V}
  {seq : ℕ → V}
  {m : ℕ}
-- given
  (hadj : ∀ n : ℕ, G.Adj (seq n) (seq (n + 1)))
  (hinj : ∀ i j, i ≤ m → j ≤ m → seq i = seq j → i = j) :
-- imply
  (consWalk G seq hadj m).support.Nodup := by
-- proof
  induction m generalizing seq hadj with
  | zero => simp [consWalk, DirectedWalk.support]
  | succ m ih =>
    simp only [consWalk, DirectedWalk.support, List.nodup_cons]
    constructor
    · rw [mem_consWalk_support]
      intro ⟨i, hi, heq⟩
      exact absurd (hinj 0 (i + 1) (Nat.zero_le _) (by omega) heq) (by omega)
    · exact ih _ _ (fun i j hi hj heq => by
      have := hinj (i + 1) (j + 1) (by omega) (by omega) heq; omega)

end DirectedCycles

namespace DirectedCycles

/--
[consWalk_tail_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma consWalk_tail_nodup
  {G : Digraph V}
  {seq : ℕ → V}
  {m : ℕ}
-- given
  (hadj : ∀ n : ℕ, G.Adj (seq n) (seq (n + 1)))
  (hm : 0 < m)
  (hinj : ∀ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → seq i = seq j → i = j) :
-- imply
  (consWalk G seq hadj m).support.tail.Nodup := by
-- proof
  cases m with
  | zero => omega
  | succ m =>
    simp only [consWalk, DirectedWalk.support, List.tail_cons]
    exact consWalk_support_nodup G _ _ m (fun i j hi hj heq => by
      have := hinj (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) heq; omega)

end DirectedCycles

namespace DirectedCycles

/--
[DirectedWalk.support_cast](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma DirectedWalk.support_cast
  {u v u' v' : V}
  {G : Digraph V}
  {p : DirectedWalk G u v}
-- given
  (hu : u = u')
  (hv : v = v') :
-- imply
  (p.cast hu hv).support = p.support := by
-- proof
  subst hu; subst hv; rfl

end DirectedCycles

namespace DirectedCycles

/--
[cycle_of_successor_labeling](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma cycle_of_successor_labeling
  {G : Digraph V}
  [Fintype V]
  [DecidableRel G.Adj]
  [DecidableEq V]
  [Nonempty V]
  {k : ℕ}
  [NeZero k]
  {f : V → ZMod k}
-- given
  (hf : IsSuccessorLabeling G k f) :
-- imply
  HasDirectedCycleDivisibleBy G k := by
-- proof
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  let next : V → V := fun v => (hf v).choose
  have hnext_adj : ∀ v, G.Adj v (next v) := fun v => (hf v).choose_spec.1
  have hnext_label : ∀ v, f (next v) = f v + 1 := fun v => (hf v).choose_spec.2
  let seq : ℕ → V := fun n => next^[n] v₀
  have hseq_adj : ∀ n, G.Adj (seq n) (seq (n + 1)) := by
    intro n; simp only [seq, Function.iterate_succ', Function.comp_apply]; exact hnext_adj _
  have hlabel : ∀ n, f (seq n) = f v₀ + (n : ZMod k) := by
    intro n; induction n with
    | zero => simp [seq]
    | succ n ih =>
      simp only [seq, Function.iterate_succ', Function.comp_apply]
      rw [hnext_label, ih]; push_cast; ring
  have hexists' : ∃ j : ℕ, 0 < j ∧ ∃ i, i < j ∧ seq i = seq j := by
    by_contra h; push Not at h
    have hinj : Function.Injective (fun i : Fin (Fintype.card V + 1) => seq i) := by
      intro a b hab; by_contra hne
      obtain h1 | h1 := Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne)
      · exact h _ (by omega) _ h1 hab
      · exact h _ (by omega) _ h1 hab.symm
    exact absurd (Fintype.card_le_of_injective _ hinj) (by simp [Fintype.card_fin])
  set j := Nat.find hexists'
  obtain ⟨hj_pos, i, hij, hseq_eq⟩ := Nat.find_spec hexists'
  have hseq_inj : ∀ a b, a < j → b < j → seq a = seq b → a = b := by
    intro a b ha hb hab; by_contra hne
    obtain h1 | h1 := Nat.lt_or_gt_of_ne hne
    · exact Nat.find_min hexists' hb ⟨by omega, a, h1, hab⟩
    · exact Nat.find_min hexists' ha ⟨by omega, b, h1, hab.symm⟩
  have hm_pos : 0 < j - i := Nat.sub_pos_of_lt hij
  let shifted : ℕ → V := fun n => seq (i + n)
  have hshifted_adj : ∀ n, G.Adj (shifted n) (shifted (n + 1)) := by
    intro n; show G.Adj (seq (i + n)) (seq (i + n + 1)); exact hseq_adj _
  have hclosed : shifted (j - i) = shifted 0 := by
    show seq (i + (j - i)) = seq (i + 0)
    rw [Nat.add_sub_cancel' hij.le, Nat.add_zero]; exact hseq_eq.symm
  let w := (consWalk G shifted hshifted_adj (j - i)).cast rfl hclosed
  have hdvd : k ∣ (j - i) := by
    have hfeq : (i : ZMod k) = (j : ZMod k) := by
      have := congr_arg f hseq_eq; rw [hlabel, hlabel] at this; exact add_left_cancel this
    have h2 : ((j - i : ℕ) : ZMod k) = 0 := by
      rw [Nat.cast_sub hij.le]; exact sub_eq_zero_of_eq hfeq.symm
    exact (ZMod.natCast_eq_zero_iff (j - i) k).mp h2
  refine ⟨shifted 0, w, ⟨?_, ?_⟩, ?_⟩
  ·
    rw [DirectedWalk.length_cast, consWalk_length]; exact hm_pos
  ·
    rw [DirectedWalk.support_cast]
    apply consWalk_tail_nodup _ _ _ _ hm_pos
    intro a b ha hb ha' hb' heq
    have ha_le : i + a ≤ j := by
      have h1 : a ≤ j - i := hb
      have h2 : j - i + i = j := Nat.sub_add_cancel hij.le
      linarith
    have hb_le : i + b ≤ j := by
      have h1 : b ≤ j - i := hb'
      have h2 : j - i + i = j := Nat.sub_add_cancel hij.le
      linarith
    by_cases ha_eq : i + a = j
    · by_cases hb_eq : i + b = j
      · omega
      ·
        exfalso
        have : seq (i + a) = seq (i + b) := heq
        rw [ha_eq] at this
        have hb_lt : i + b < j := Nat.lt_of_le_of_ne hb_le hb_eq
        have : seq j = seq (i + b) := this
        rw [← hseq_eq] at this
        have := hseq_inj i (i + b) hij hb_lt this
        omega
    · have ha_lt : i + a < j := Nat.lt_of_le_of_ne ha_le ha_eq
      by_cases hb_eq : i + b = j
      · exfalso
        have : seq (i + a) = seq (i + b) := heq
        rw [hb_eq] at this
        rw [← hseq_eq] at this
        have := hseq_inj i (i + a) hij ha_lt this.symm
        omega
      · have hb_lt : i + b < j := Nat.lt_of_le_of_ne hb_le hb_eq
        have := hseq_inj (i + a) (i + b) ha_lt hb_lt heq
        omega
  ·
    rw [DirectedWalk.length_cast, consWalk_length]; exact hdvd

end DirectedCycles

namespace DirectedCycles

/--
[exists_nat_le_div_one_add_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean)
-/
@[path]
lemma exists_nat_le_div_one_add_log
  {k : ℕ}
-- given
  (hk : k ≥ 1) :
-- imply
  ∃ d : ℕ, d ≥ 1 ∧ (k : ℝ) ≤ (d : ℝ) / (1 + Real.log (1 + (d : ℝ) * (d : ℝ))) := by
-- proof
  refine ⟨25 * k ^ 2, ?_, ?_⟩
  · have : k ^ 2 ≥ 1 := Nat.one_le_pow 2 k (by omega)
    omega
  · have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hd_cast : ((25 * k ^ 2 : ℕ) : ℝ) = 25 * (k : ℝ) ^ 2 := by push_cast; ring
    rw [hd_cast]
    set K := (k : ℝ)
    have h_sq : (1 : ℝ) + 25 * K ^ 2 * (25 * K ^ 2) ≤ (25 * K ^ 2 + 1) ^ 2 := by
      nlinarith [sq_nonneg K]
    have h_log_bound : Real.log (1 + 25 * K ^ 2 * (25 * K ^ 2)) ≤
      2 * Real.log (25 * K ^ 2 + 1) := by
      calc Real.log (1 + 25 * K ^ 2 * (25 * K ^ 2))
        ≤ Real.log ((25 * K ^ 2 + 1) ^ 2) := Real.log_le_log (by positivity) h_sq
        _ = 2 * Real.log (25 * K ^ 2 + 1) := by rw [Real.log_pow]; ring
    have h_log_sqrt : Real.log (25 * K ^ 2 + 1) ≤ 2 * Real.sqrt (25 * K ^ 2 + 1) := by
      have h := Real.log_le_rpow_div (x := 25 * K ^ 2 + 1) (ε := 1/2)
        (by positivity) (by norm_num)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    have h_sqrt_bound : Real.sqrt (25 * K ^ 2 + 1) ≤ 5 * K + 1 := by
      rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 5 * K + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have h_denom_bound : 1 + Real.log (1 + 25 * K ^ 2 * (25 * K ^ 2)) ≤ 20 * K + 5 := by
      linarith
    have h_denom_pos : (0 : ℝ) < 1 + Real.log (1 + 25 * K ^ 2 * (25 * K ^ 2)) := by
      have : (0 : ℝ) ≤ Real.log (1 + 25 * K ^ 2 * (25 * K ^ 2)) :=
        Real.log_nonneg (by nlinarith)
      linarith
    have h_ratio : K ≤ 25 * K ^ 2 / (20 * K + 5) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 20 * K + 5)]
      nlinarith [sq_nonneg K, sq_nonneg (K - 1)]
    calc K ≤ 25 * K ^ 2 / (20 * K + 5) := h_ratio
      _ ≤ 25 * K ^ 2 / (1 + Real.log (1 + 25 * K ^ 2 * (25 * K ^ 2))) := by
        apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 25 * K ^ 2)
          h_denom_pos h_denom_bound

end DirectedCycles


-- created on 2026-10-23
