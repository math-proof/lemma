import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part7
set_option doc.verso.suggestions false


namespace Remark_1_3_10

lemma binaryToTernary_props : BinaryToTernaryProperties binaryToTernary :=
  Classical.choose_spec binaryToTernary_exists

/-- {lean}`binaryToTernary x = 0` iff {lean}`x = 0` for x ∈ \[0,1\]. -/
lemma binaryToTernary_eq_zero_iff {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    binaryToTernary x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx_ne
    have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_ne)
    have h0_in : (0:ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, by norm_num⟩
    have h_mono := binaryToTernary_props.monotone_on h0_in hx (le_of_lt hx_pos)
    rw [binaryToTernary_props.zero_at_zero] at h_mono
    have h_zero_set : Set.Icc (0:ℝ) x ⊆ Set.Icc 0 1 ∩ {y | binaryToTernary y = 0} := by
      intro y hy
      constructor
      · exact ⟨hy.1, le_trans hy.2 hx.2⟩
      · simp only [Set.mem_setOf_eq]
        have h0y : (0:ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, by norm_num⟩
        have hy_in : y ∈ Set.Icc 0 1 := ⟨hy.1, le_trans hy.2 hx.2⟩
        have h_mono1 := binaryToTernary_props.monotone_on h0y hy_in hy.1
        have h_mono2 := binaryToTernary_props.monotone_on hy_in hx hy.2
        rw [binaryToTernary_props.zero_at_zero] at h_mono1
        rw [h] at h_mono2
        linarith [binaryToTernary_props.nonneg y]
    have h_uncountable : ¬ (Set.Icc (0:ℝ) x).Countable := by
      have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (fun h => hx_ne h.symm)
      have h_card := Cardinal.mk_Icc_real hx_pos
      intro hc
      have := hc.le_aleph0
      rw [h_card] at this
      exact Cardinal.aleph0_lt_continuum.not_ge this
    exact h_uncountable (Set.Countable.mono h_zero_set binaryToTernary_props.zero_set_countable)
  · intro h
    rw [h]
    exact binaryToTernary_props.zero_at_zero

end Remark_1_3_10
