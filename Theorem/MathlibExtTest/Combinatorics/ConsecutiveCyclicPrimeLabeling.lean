/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean -/


import Instance.Combinatorics.ConsecutiveCyclicPrimeLabeling.Part2
import Lemma.Finset.ConsecutiveCyclicPrimeLabeling


namespace MetaMathlibExt

-- The empty ladder is rejected at every offset.
example (o : ℕ) : ¬ IsConsecutiveCyclicPrimeLabeling 0 o := by
  rintro ⟨h, _⟩
  exact Nat.lt_irrefl 0 h

example : ¬ IsConsecutiveCyclicPrimeLabeling 0 0 := by decide

-- Label range endpoints at the first and last perimeter positions (n = 4, offset 7).
example : cyclicLabel 4 7 ⟨0, by decide⟩ = 8 := by decide

example : cyclicLabel 4 7 ⟨7, by decide⟩ = 7 := by decide

example :
    1 ≤ cyclicLabel 4 7 ⟨0, by decide⟩ ∧ cyclicLabel 4 7 ⟨0, by decide⟩ ≤ 2 * 4 :=
  cyclicLabel_mem_range 4 7 (by decide) _

example :
    1 ≤ cyclicLabel 4 7 ⟨7, by decide⟩ ∧ cyclicLabel 4 7 ⟨7, by decide⟩ ≤ 2 * 4 :=
  cyclicLabel_mem_range 4 7 (by decide) _

-- `P_1 x P_2` admits a consecutive cyclic prime labeling.
example : IsConsecutiveCyclicPrimeLabeling 1 0 := by decide

-- Source `P_4 x P_2` rotation: top row `v_1, ..., v_4 = 8, 1, 2, 3`
-- (first position checked above).
example : cyclicLabel 4 7 ⟨1, by decide⟩ = 1 := by decide

example : cyclicLabel 4 7 ⟨2, by decide⟩ = 2 := by decide

example : cyclicLabel 4 7 ⟨3, by decide⟩ = 3 := by decide

-- Same rotation: perimeter order `u_4, u_3, u_2, u_1 = 4, 5, 6, 7`,
-- i.e. bottom row `u_1, ..., u_4 = 7, 6, 5, 4`.
example : cyclicLabel 4 7 ⟨4, by decide⟩ = 4 := by decide

example : cyclicLabel 4 7 ⟨5, by decide⟩ = 5 := by decide

example : cyclicLabel 4 7 ⟨6, by decide⟩ = 6 := by decide

example : cyclicLabel 4 7 ⟨7, by decide⟩ = 7 := by decide

-- The full `P_4 x P_2` rotation is a valid consecutive cyclic prime labeling.
example : IsConsecutiveCyclicPrimeLabeling 4 7 := by decide

-- Another offset on the same small ladder fails coprimality
-- (`v_3 = 3` meets `u_3 = 6` on a rung).
example : ¬ IsConsecutiveCyclicPrimeLabeling 4 0 := by decide

end MetaMathlibExt
