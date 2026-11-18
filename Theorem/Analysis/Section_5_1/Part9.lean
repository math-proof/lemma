module

public import Mathlib
public import Theorem.Analysis.Section_4_3.Part2
public import Abbrev.Analysis.Section_5_1.Part8
public import Abbrev.Analysis.Section_5_1.Part6
public import Theorem.Analysis.Section_5_1.Part5
set_option doc.verso.suggestions false

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

public section


namespace Chapter5

/-- Definition 5.1.12 (bounded sequences) -/
public theorem Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

public theorem IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

/-- Cauchy sequences are bounded. -/
public theorem Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  obtain ⟨N, hN, hsteady⟩ := h (1:ℚ) (by norm_num)
  set n1 : ℤ := max a.n₀ N
  have hn1 : (a.from N).n₀ = n1 := rfl
  have seq_from (n : ℤ) (hn : n ≥ n1) : (a.from N).seq n = a.seq n := by
    dsimp [Sequence.from, Sequence.mk']
    split
    · rfl
    · omega
  have htail (n : ℤ) (hn : n ≥ n1) : |a.seq n| ≤ 1 + |a.seq n1| := by
    have hn_from : (a.from N).n₀ ≤ n := by rw [hn1]; exact hn
    have hn1_from : (a.from N).n₀ ≤ n1 := by rw [hn1]
    have hclose := hsteady n hn_from n1 hn1_from
    rw [Section_4_3.close_iff, seq_from n hn, seq_from n1 le_rfl] at hclose
    calc
      |a.seq n| = |(a.seq n - a.seq n1) + a.seq n1| := by ring
      _ ≤ |a.seq n - a.seq n1| + |a.seq n1| := abs_add_le _ _
      _ ≤ 1 + |a.seq n1| := by linarith
  let k : ℕ := Int.toNat (n1 - a.n₀)
  let init : Fin (k + 1) → ℚ := fun i => a.seq (a.n₀ + (i : ℤ))
  obtain ⟨M0, hM0nonneg, hM0⟩ := IsBounded.finite init
  refine ⟨max M0 (1 + |a.seq n1|), by positivity, ?_⟩
  intro n
  by_cases hn0 : n < a.n₀
  · have hs0 : a.seq n = 0 := a.vanish n hn0
    simp only [hs0, abs_zero]
    exact le_trans hM0nonneg (le_max_left _ _)
  · by_cases hnt : n1 ≤ n
    · exact (htail n hnt).trans (le_max_right _ _)
    · have hn_ge : a.n₀ ≤ n := le_of_not_gt hn0
      have hn_lt : n < n1 := lt_of_not_ge hnt
      have hdiff_nonneg : 0 ≤ n - a.n₀ := sub_nonneg.mpr hn_ge
      have hcast : (n - a.n₀).toNat < k + 1 := by
        have h1 : ((n - a.n₀).toNat : ℤ) = n - a.n₀ := Int.toNat_of_nonneg hdiff_nonneg
        have h2 : ((n1 - a.n₀).toNat : ℤ) = n1 - a.n₀ :=
          Int.toNat_of_nonneg (sub_nonneg.mpr (le_trans (le_max_left a.n₀ N) (le_rfl)))
        change (n - a.n₀).toNat < (n1 - a.n₀).toNat + 1
        omega
      set i : Fin (k + 1) := ⟨(n - a.n₀).toNat, hcast⟩
      have hseq : init i = a.seq n := by
        dsimp [init, i]
        have : a.n₀ + ((n - a.n₀).toNat : ℤ) = n := by
          have := Int.toNat_of_nonneg hdiff_nonneg
          omega
        rw [this]
      have : |a.seq n| ≤ M0 := by
        rw [← hseq]
        exact hM0 i
      exact this.trans (le_max_left _ _)

end Chapter5
