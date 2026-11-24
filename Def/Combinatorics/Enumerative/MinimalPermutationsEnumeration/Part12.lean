module
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Fin.Basic
public import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

noncomputable def mpePerms (d : ℕ) : Finset (Equiv.Perm (Fin (d + 2))) := by
  classical
  exact Finset.univ.filter (mpeGood d)

def mpePositions (d : ℕ) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun a => 0 < a.val ∧ a.val < d

def mpeAllowed (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    Finset (Finset (Fin (d + 2))) :=
  Finset.powersetCard (a.val + 1) Finset.univ \ (exclA d a hpos ∪ exclB d a)

noncomputable def mpeFiber (d : ℕ) (a : Fin (d + 1)) :
    Finset (Equiv.Perm (Fin (d + 2))) :=
  (mpePerms d).filter fun σ => mpeAscentPos d σ = a

end MetaMathlibExt
end
