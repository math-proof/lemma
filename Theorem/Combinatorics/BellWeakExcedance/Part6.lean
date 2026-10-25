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
import Def.Combinatorics.BellWeakExcedance.Part6


section

namespace MetaMathlibExt

theorem pred_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : pred P u hu ∈ P.part u := by
  have hmem : pred P u hu ∈ (P.part u).filter (fun x => x < u) := by
    unfold pred
    exact Finset.max'_mem _ _
  exact Finset.mem_of_mem_filter _ hmem

theorem pred_lt {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : pred P u hu < u := by
  have hmem : pred P u hu ∈ (P.part u).filter (fun x => x < u) := by
    unfold pred
    exact Finset.max'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

theorem le_pred_of_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u x : Fin n}
    (hu : u ∉ mins P) (hxB : x ∈ P.part u) (hxu : x < u) :
    x ≤ pred P u hu := by
  have hmem : x ∈ (P.part u).filter (fun y => y < u) :=
    Finset.mem_filter.mpr ⟨hxB, hxu⟩
  unfold pred
  exact Finset.le_max' _ _ hmem

end MetaMathlibExt
end
