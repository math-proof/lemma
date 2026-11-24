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
public import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

def mpeGood (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) : Prop :=
  (Finset.univ.filter fun i : Fin (d + 1) =>
    σ i.castSucc > σ i.succ).card = d ∧
  ∀ j : Fin (d + 2),
    (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d

end MetaMathlibExt
end
