module
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.GroupTheory.Perm.Fin
public import Def.Combinatorics.Enumerative.Stirling.Part4
public import Theorem.Finset.Enumerative.Stirling
public import Instance.Combinatorics.Enumerative.ZagierCyclicPermutationProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/
namespace MetaMathlibExt

def zagExceedance {n : ℕ} (e π : Equiv.Perm (Fin n)) (x : Fin n) : Prop :=
  e.symm x < e.symm (π x)

def zagTrivialAntiExceedance {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : Prop :=
  π x = e (zagCycleMinPos e π x)

def zagNontrivialAntiExceedance {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : Prop :=
  ¬zagExceedance e π x ∧ ¬zagTrivialAntiExceedance e π x

end MetaMathlibExt
