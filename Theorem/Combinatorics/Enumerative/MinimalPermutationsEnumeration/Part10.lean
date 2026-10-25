/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part9


section

namespace MetaMathlibExt

theorem mpeConstructFun_mem_left (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (p : Fin (d + 2)) (hp : p.val ≤ a.val) :
    mpeConstructFun d a L hL p ∈ L := by
  simp only [mpeConstructFun, hp, ↓reduceDIte]
  exact Finset.orderEmbOfFin_mem L hL _

theorem mpeConstructFun_not_mem_right (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (p : Fin (d + 2)) (hp : ¬p.val ≤ a.val) :
    mpeConstructFun d a L hL p ∉ L := by
  simp only [mpeConstructFun, hp, ↓reduceDIte]
  exact Finset.mem_compl.mp
    (Finset.orderEmbOfFin_mem Lᶜ (mpe_compl_card d a L hL) _)

theorem mpeConstructFun_injective (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    Function.Injective (mpeConstructFun d a L hL) := by
  intro p q heq
  by_cases hp : p.val ≤ a.val
  · by_cases hq : q.val ≤ a.val
    · have heq' := heq
      simp only [mpeConstructFun, hp, hq, ↓reduceDIte] at heq'
      have hi := (L.orderEmbOfFin hL).injective heq'
      have hirev := Fin.rev_injective hi
      apply Fin.ext
      have hv := congrArg Fin.val hirev
      simpa only [mpeFirstIndex_val] using hv
    · have hpL := mpeConstructFun_mem_left d a L hL p hp
      have hqL := mpeConstructFun_not_mem_right d a L hL q hq
      exact absurd (heq ▸ hpL) hqL
  · by_cases hq : q.val ≤ a.val
    · have hpL := mpeConstructFun_not_mem_right d a L hL p hp
      have hqL := mpeConstructFun_mem_left d a L hL q hq
      exact absurd (heq.symm ▸ hqL) hpL
    · have heq' := heq
      simp only [mpeConstructFun, hp, hq, ↓reduceDIte] at heq'
      have hi := (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)).injective heq'
      have hirev := Fin.rev_injective hi
      apply Fin.ext
      have hv := congrArg Fin.val hirev
      simp only [mpeSecondIndex_val] at hv
      omega

end MetaMathlibExt
end
