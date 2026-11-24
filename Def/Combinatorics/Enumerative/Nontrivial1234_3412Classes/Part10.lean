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
public import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def ntBreakMap {m : ℕ} (y v : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) (z : Fin m) : Fin (m + 1) :=
  let w := y.succAbove z
  if finRotate (m + 1) w = y then
    if w ∈ ntBreaks (ntIns y v ρ) then w else y
  else w

def ntSemi {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ j : ℕ, ∃ hj : j + 1 ≤ n, π = ntBeta n j hj

end MetaMathlibExt
