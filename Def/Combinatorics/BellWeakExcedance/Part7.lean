/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Theorem.Combinatorics.BellWeakExcedance.Part6


section

namespace MetaMathlibExt

noncomputable def succ {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (y : Fin n)
    (hy : y ∉ maxs P) : Fin n :=
  ((P.part y).filter (fun x => y < x)).min'
    (by
      have hpart_mem : P.part y ∈ P.parts := P.part_mem.mpr (Finset.mem_univ y)
      have hne : (P.part y).Nonempty := P.nonempty_of_mem_parts hpart_mem
      have hmax_mem : (P.part y).max' hne ∈ P.part y := Finset.max'_mem _ _
      have hmax_le : ∀ x ∈ P.part y, x ≤ (P.part y).max' hne :=
        fun x hx => Finset.le_max' _ _ hx
      have hmax_eq : (P.part y).max' hne ∈ maxs P := by
        rw [mem_maxs_iff]
        exact ⟨P.part y, hpart_mem, hmax_mem, hmax_le⟩
      have hne_max : (P.part y).max' hne ≠ y := fun h => hy (h ▸ hmax_eq)
      have hlt : y < (P.part y).max' hne :=
        lt_of_le_of_ne (hmax_le y (P.mem_part (Finset.mem_univ y))) (Ne.symm hne_max)
      exact ⟨(P.part y).max' hne, Finset.mem_filter.mpr ⟨hmax_mem, hlt⟩⟩)

end MetaMathlibExt
end
