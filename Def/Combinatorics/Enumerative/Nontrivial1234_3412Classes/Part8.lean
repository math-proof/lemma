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
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part7


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
