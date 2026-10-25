/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part8
open SimpleGraph


section

namespace MetaMathlibExt

noncomputable def partnerT (m : ℕ) (t : Tiling m ∅) :
    Fin 4 × Fin m → Fin 4 × Fin m :=
  fun v =>
    let a := v.1
    let i := v.2
    let j := i.val
    let above := getS m ∅ t j
    let below := if j = 0 then ∅ else getS m ∅ t (j - 1)
    if h_up : a ∈ above then
      have hj1 : j + 1 < m := by
        have hjlt : j < m := i.isLt
        by_cases hm0 : m = 0
        · subst hm0
          have hempty : above = ∅ := by
            unfold above
            have : getS 0 ∅ t j = ∅ := rfl
            exact this
          rw [hempty] at h_up
          exact absurd h_up (Finset.notMem_empty a)
        · by_contra hcon
          have hle : m ≤ j + 1 := by omega
          have heq : j + 1 = m := by omega
          have hjpred : j = m - 1 := by omega
          have hempty : above = ∅ := by
            unfold above
            rw [hjpred]
            exact getS_pred_top_empty m t (by omega)
          rw [hempty] at h_up
          exact absurd h_up (Finset.notMem_empty a)
      (a, ⟨j + 1, hj1⟩)
    else if h_down : a ∈ below then
      have hj0 : j ≠ 0 := by
        intro hcon
        have hbelow_eq : below = ∅ := by
          unfold below
          simp only [ite_eq_left hcon]
        rw [hbelow_eq] at h_down
        exact absurd h_down (Finset.notMem_empty a)
      have hj1 : j - 1 < m := by
        have : j < m := i.isLt
        omega
      (a, ⟨j - 1, hj1⟩)
    else
      (getF m ∅ t j a, i)

end MetaMathlibExt
end
