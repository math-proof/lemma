/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
public import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part13

@[expose] public section

namespace MetaMathlibExt

def ntStartBad {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) :
    Finset (Fin (k + 2)) :=
  (if σ 1 = Fin.last (k + 1) then {0} else ∅) ∪
    (if σ 0 = (⟨k, by omega⟩ : Fin (k + 2))
      then {σ.symm (Fin.last (k + 1))} else ∅)

def ntEndBad {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) :
    Finset (Fin (k + 2)) :=
  (if σ (⟨k, by omega⟩ : Fin (k + 2)) = 0
      then {Fin.last (k + 1)} else ∅) ∪
    (if σ (Fin.last (k + 1)) = 1 then {σ.symm 0} else ∅)

def ntEBad {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) :
    Finset (Fin (k + 2)) := ntStartBad σ ∪ ntEndBad σ

end MetaMathlibExt
