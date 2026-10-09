import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[path]
private lemma main
-- given
  (s : Finset ι)
  (H : s.Nonempty)
  (g : ι → ℝ)
  (c : ℝ) :
-- imply
  s.sup' H (fun i => g i + c) = s.sup' H g + c := by
-- proof
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i hi => add_le_add_left (Finset.le_sup' g hi) c
  ·
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' H g
    rw [he]
    exact Finset.le_sup' (f := fun i => g i + c) hi


-- created on 2026-10-07
