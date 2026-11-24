module
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Def.Combinatorics.BellWeakExcedance.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
