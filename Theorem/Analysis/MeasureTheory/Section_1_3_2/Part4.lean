import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part4
set_option doc.verso.suggestions false


/-- Dyadic rationals are countable. -/
lemma DyadicRationals.countable : DyadicRationals.Countable := by
  let D' := ⋃ n : ℕ, (fun k : Fin (2^n + 1) => (k : ℝ) / 2^n) '' Set.univ
  have hD'_countable : D'.Countable :=
    Set.countable_iUnion (fun n => Set.Countable.image Set.countable_univ _)
  apply Set.Countable.mono _ hD'_countable
  intro x ⟨k, n, hk, hk_le⟩
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and, D']
  use n
  have hk_lt : k < 2^n + 1 := Nat.lt_succ_of_le hk_le
  exact ⟨⟨k, hk_lt⟩, hk.symm⟩

