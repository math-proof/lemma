/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean -/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Theorem.NumberTheory.MultipleZeta.Index.Part2
public import Theorem.Nat.MultipleZeta.Index
public import Def.NumberTheory.MultipleZeta.Series.Part2
@[expose] public section

/-!
# Multiple-zeta and multiple-zeta-star series

This file defines multiple-zeta summands and values using strictly decreasing positive summation
variables, and multiple-zeta-star summands and values using weakly decreasing positive summation
variables. The star convention follows arXiv:2307.09867 and arXiv:2309.07569.
-/


namespace MetaMathlibExt.MultipleZeta

/-- Weakly decreasing tuples `m₀ ≥ m₁ ≥ ⋯` of positive natural numbers.
Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
abbrev WeaklyDecreasingTuple (depth : ℕ) :=
  {m : Fin depth → PNat // Antitone m}

end MetaMathlibExt.MultipleZeta
