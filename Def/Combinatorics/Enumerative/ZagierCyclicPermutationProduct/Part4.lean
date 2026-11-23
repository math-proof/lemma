/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.GroupTheory.Perm.Fin
public import Def.Combinatorics.Enumerative.Stirling.Part4
public import Theorem.Finset.Enumerative.Stirling
public import Structure.Combinatorics.Enumerative.ZagierCyclicPermutationProduct

@[expose] public section

/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def ZagMarkedTriple.toFinset {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) : Finset (Fin n) :=
  {m.first, m.middle, m.third}

end MetaMathlibExt
