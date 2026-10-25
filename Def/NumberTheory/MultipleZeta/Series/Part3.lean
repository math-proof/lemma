/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean -/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
import Abbrev.NumberTheory.MultipleZeta.Series.Part2
/-!
# Multiple-zeta and multiple-zeta-star series

This file defines multiple-zeta summands and values using strictly decreasing positive summation
variables, and multiple-zeta-star summands and values using weakly decreasing positive summation
variables. The star convention follows arXiv:2307.09867 and arXiv:2309.07569.
-/


namespace MetaMathlibExt.MultipleZeta

/-- The unique weakly decreasing tuple of length zero. -/
def WeaklyDecreasingTuple.empty : WeaklyDecreasingTuple 0 :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- Every strictly decreasing tuple is weakly decreasing. -/
def StrictDecreasingTuple.toWeaklyDecreasing {depth : ℕ}
    (m : StrictDecreasingTuple depth) : WeaklyDecreasingTuple depth :=
  ⟨m.1, m.2.antitone⟩

/-- The reciprocal product `(∏ i, mᵢ ^ kᵢ)⁻¹` attached to a weakly decreasing tuple `m`.
Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
noncomputable def starSummand (index : Index)
    (m : WeaklyDecreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

/-- The multiple-zeta-star series over weakly decreasing tuples.
Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
@[nolint unusedArguments]
noncomputable def starValue (index : Index) (_h : index.IsAdmissibleOrEmpty) : ℝ :=
  ∑' m : WeaklyDecreasingTuple index.depth, starSummand index m

end MetaMathlibExt.MultipleZeta
