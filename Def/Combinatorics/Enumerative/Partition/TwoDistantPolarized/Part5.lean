/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part4


namespace MetaMathlibExt.TwoDistantPolarized

open List

def Aset (n : ℕ) := {p : Nat.Partition n //
  p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b}

noncomputable def e1 (n : ℕ) : Aset n ≃ Omega n where
  toFun x := ⟨toB (sl x.1),
    toB_pairwise _ (hA_iff x.1 |>.mp x.2) (sl_pos x.1), by
      have hft := fromB_toB (sl x.1) (hA_iff x.1 |>.mp x.2) (sl_pos x.1)
      have hs := sum_fromB (toB (sl x.1))
      rw [hft, sl_sum] at hs; omega⟩
  invFun y := ⟨ofList (fromB y.1) (fromB_pos y.1) (by rw [sum_fromB, y.2.2]),
     (hA_iff _).mpr (by
        rw [sl_ofList (fromB y.1) (fromB_pos y.1) (by rw [sum_fromB, y.2.2])
          ((fromB_pairwise y.1 y.2.1).imp (fun h => by omega))]
        exact fromB_pairwise y.1 y.2.1)⟩
  left_inv x := by
    apply Subtype.ext
    apply Nat.Partition.ext
    dsimp only
    rw [ofList_parts, fromB_toB (sl x.1) (hA_iff x.1 |>.mp x.2) (sl_pos x.1), sl, Multiset.sort_eq]
  right_inv y := by
    apply Subtype.ext
    dsimp only
    rw [sl_ofList (fromB y.1) (fromB_pos y.1) (by rw [sum_fromB, y.2.2])
      ((fromB_pairwise y.1 y.2.1).imp (fun h => by omega))]
    exact toB_fromB y.1

/-- staircase with offset j: builds the even parts from the odd b-values -/
def Qof (j : ℕ) (o : List ℕ) : List ℕ := o.mapIdx (fun s x => x + (2*(j+s)+1))

end MetaMathlibExt.TwoDistantPolarized
