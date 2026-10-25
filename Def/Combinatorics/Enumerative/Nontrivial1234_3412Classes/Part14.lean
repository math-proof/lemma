/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part13


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
