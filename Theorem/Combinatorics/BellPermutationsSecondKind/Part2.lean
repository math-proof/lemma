/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Def.Combinatorics.BellPermutationsSecondKind.Part2


namespace MetaMathlibExt

theorem numWeak_bellPerm {n : ℕ} {f : Fin n → Fin n} (hf : IsRGF f) :
    numWeak (bellPerm f) = numVals f := by
  have hsd := rgf_subdiag hf
  have hset : Finset.univ.filter (fun i => i ≤ bellPerm f i) = Finset.univ.image f := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      by_contra hc
      simp only [not_exists] at hc
      have hlt := sigma_lt_of_novalue i (rgf_novalue_lt hf i hc)
      have hi' : i.val ≤ (bellPerm f i).val := hi
      omega
    · rintro ⟨j, hj⟩
      exact sigma_ge_of_value hsd i ⟨j, hj⟩
  unfold numWeak numVals
  rw [Fintype.card_subtype, hset]

end MetaMathlibExt
