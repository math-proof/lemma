/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean -/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
import Abbrev.NumberTheory.MultipleZeta.Series
/-!
# Multiple-zeta and multiple-zeta-star series

This file defines multiple-zeta summands and values using strictly decreasing positive summation
variables, and multiple-zeta-star summands and values using weakly decreasing positive summation
variables. The star convention follows arXiv:2307.09867 and arXiv:2309.07569.
-/


namespace MetaMathlibExt.MultipleZeta

/-- The unique strictly decreasing tuple of length zero. -/
def StrictDecreasingTuple.empty : StrictDecreasingTuple 0 :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- The reciprocal product `(∏ i, mᵢ ^ kᵢ)⁻¹` attached to a decreasing tuple `m`.
Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
noncomputable def strictSummand (index : Index)
    (m : StrictDecreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

/-- An index on which the ordinary strict multiple-zeta value is defined: either admissible or the
empty index. -/
def Index.IsAdmissibleOrEmpty (index : Index) : Prop :=
  index.IsAdmissible ∨ index.depth = 0

/-- The ordinary strict multiple-zeta series over decreasing tuples.
Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
@[nolint unusedArguments]
noncomputable def strictValue (index : Index) (_h : index.IsAdmissibleOrEmpty) : ℝ :=
  ∑' m : StrictDecreasingTuple index.depth, strictSummand index m

end MetaMathlibExt.MultipleZeta
