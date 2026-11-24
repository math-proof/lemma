module
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.GroupTheory.Perm.Fin
public import Def.Combinatorics.Enumerative.Stirling.Part4
public import Theorem.Finset.Enumerative.Stirling
public import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part20


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

noncomputable def zagSliceMarked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) : Finset (Fin n) :=
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  {zagCycleMinPos e' π' (e (zagCycleMinPos e π ε)),
    zagCycleMinPos e' π' (π ε),
    zagCycleMinPos e' π' (e (zagCutPos e π ε hε))}

end MetaMathlibExt
