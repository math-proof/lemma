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
public import Lemma.Finset.Enumerative.Stirling
public import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part30
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/
public section




namespace MetaMathlibExt

structure ZagFullSliceResult {n : ℕ} (p : ZagPointedPlane n) where
  out : ZagOddMarkedPlane n
  root_eq : out.root = zagCycleMinPos p.order p.vertical p.point
  preserves_before : ∀ r : Fin n,
    r < zagCycleMinPos p.order p.vertical p.point →
    r ∈ zagCycleMinima p.order p.vertical →
    r ∈ zagCycleMinima out.order out.vertical

end MetaMathlibExt
