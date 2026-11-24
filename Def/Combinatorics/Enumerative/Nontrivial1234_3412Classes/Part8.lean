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
public import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

/-- The two-block permutation. -/
def ntBeta (n j : ℕ) (hj : j + 1 ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (ntBetaFun n j hj) (fun i => ntBeta_invol hj i)

/-- The family obtained by composing the two-block permutation with one swap. -/
def ntT (n j : ℕ) (hj : j + 1 ≤ n) : Set (Equiv.Perm (Fin n)) :=
  {κ | ∃ P Q : Fin n, P ≠ Q ∧ κ = ntBeta n j hj * Equiv.swap P Q}

/-- The patterned part of the swap family. -/
def ntK (n j : ℕ) (hj : j + 1 ≤ n) : Set (Equiv.Perm (Fin n)) :=
  ntT n j hj ∩ {σ | ntPat n σ}

/-- The generic patterned part: extreme-avoiding patterns outside every `K`. -/
def ntG (k : ℕ) : Set (Equiv.Perm (Fin (k + 1))) :=
  {σ | σ ∈ ntE k ∧ ntPat (k + 1) σ ∧
    ∀ j : ℕ, ∀ hj : j + 1 ≤ k + 1, σ ∉ ntK (k + 1) j hj}

end MetaMathlibExt
