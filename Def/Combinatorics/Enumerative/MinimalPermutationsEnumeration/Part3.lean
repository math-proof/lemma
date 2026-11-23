/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

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
public import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part3

@[expose] public section

section

namespace MetaMathlibExt

def firstVals (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1)) :
    Finset (Fin (d + 2)) :=
  Finset.image (fun i : Fin (a.val + 1) => σ (block1Pos d a i)) Finset.univ

def secondVals (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1)) :
    Finset (Fin (d + 2)) :=
  Finset.image (fun i : Fin ((d - a.val) + 1) => σ (block2Pos d a i)) Finset.univ

end MetaMathlibExt
end
