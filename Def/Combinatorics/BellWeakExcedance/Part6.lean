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
import Theorem.Combinatorics.BellWeakExcedance.Part5


section

namespace MetaMathlibExt

noncomputable def pred {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (u : Fin n)
    (hu : u ∉ mins P) : Fin n :=
  ((P.part u).filter (fun x => x < u)).max'
    (by
      have hpart_mem : P.part u ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u)
      have hne : (P.part u).Nonempty := P.nonempty_of_mem_parts hpart_mem
      have hmin_mem : (P.part u).min' hne ∈ P.part u := Finset.min'_mem _ _
      have hmin_le : ∀ x ∈ P.part u, (P.part u).min' hne ≤ x :=
        fun x hx => Finset.min'_le _ _ hx
      have hmin_eq : (P.part u).min' hne ∈ mins P := by
        rw [mem_mins_iff]
        exact ⟨P.part u, hpart_mem, hmin_mem, hmin_le⟩
      have hne_min : (P.part u).min' hne ≠ u := fun h => hu (h ▸ hmin_eq)
      have hlt : (P.part u).min' hne < u :=
        lt_of_le_of_ne (hmin_le u (P.mem_part (Finset.mem_univ u))) hne_min
      exact ⟨(P.part u).min' hne, Finset.mem_filter.mpr ⟨hmin_mem, hlt⟩⟩)

end MetaMathlibExt
end
