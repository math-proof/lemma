module
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.GroupTheory.Perm.Fin
public import Def.Combinatorics.Enumerative.Stirling.Part4
public import Theorem.Finset.Enumerative.Stirling
public import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part8


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

def zagBlockSwap {n : ℕ} (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    Equiv.Perm (Fin n) where
  toFun p := ⟨zagBlockSwapNat a b c p,
    zagBlockSwapNat_lt hab hbc c.isLt p.isLt⟩
  invFun p := ⟨zagBlockUnswapNat a b c p,
    zagBlockUnswapNat_lt hab hbc c.isLt p.isLt⟩
  left_inv p := Fin.ext (zagBlockUnswapNat_swap (p := p) hab hbc)
  right_inv p := Fin.ext (zagBlockSwapNat_unswap (p := p) hab hbc)

end MetaMathlibExt
