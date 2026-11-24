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
public import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

noncomputable def mpeAscentPos (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) :
    Fin (d + 1) := by
  classical
  exact if h : mpeGood d σ then (mpeGood_forward d σ h).choose else 0

end MetaMathlibExt
end
