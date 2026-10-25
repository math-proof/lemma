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
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part5


namespace MetaMathlibExt

/-! ## N4: the point-insertion map for permutations. -/

/-- Forward map of point insertion. -/
def ntInsFwd {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Fin (m + 1) → Fin (m + 1) :=
  Fin.insertNth p v (fun i => v.succAbove (ρ i))

/-- Backward map of point insertion. -/
def ntInsBwd {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Fin (m + 1) → Fin (m + 1) :=
  Fin.insertNth v p (fun j => p.succAbove (ρ.symm j))

/-- Inserting a point into a permutation. -/
def ntIns {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) :=
  ⟨ntInsFwd p v ρ, ntInsBwd p v ρ,
    fun x => by
      by_cases hxp : x = p
      · subst hxp
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_same]
      · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq_iff.mpr hxp
        subst hi
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_succAbove,
          Equiv.symm_apply_apply],
    fun x => by
      by_cases hxv : x = v
      · subst hxv
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_same]
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq_iff.mpr hxv
        subst hj
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_succAbove,
          Equiv.apply_symm_apply]⟩

/-- Permutations fixing the left extreme value. -/
def ntA (k : ℕ) : Set (Equiv.Perm (Fin (k + 1))) :=
  {σ | σ 0 = Fin.last k}

/-- Permutations fixing the right extreme value. -/
def ntB (k : ℕ) : Set (Equiv.Perm (Fin (k + 1))) :=
  {σ | σ (Fin.last k) = 0}

end MetaMathlibExt
