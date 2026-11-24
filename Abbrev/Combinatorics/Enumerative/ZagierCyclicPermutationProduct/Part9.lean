module
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.GroupTheory.Perm.Fin
public import Def.Combinatorics.Enumerative.Stirling.Part4
public import Theorem.Finset.Enumerative.Stirling
public import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part39


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

abbrev ZagOddVerticalDecomposition
    (n : ℕ) (hn : 0 < n) (k : ℕ) :=
  ZagVerticalFiber n hn k 1 ⊕
    Σ d : Fin n, ZagVerticalFiber n hn k (2 * d.val + 3)

end MetaMathlibExt
