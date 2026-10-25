/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean -/

import Def.NumberTheory.MultipleZeta.Series.Part3
import Lemma.Nat.MultipleZeta.Series
import Abbrev.NumberTheory.MultipleZeta.Reversal
/-!
# Reversing multiple-zeta summation conventions

Multiple-zeta values are commonly written using either strictly increasing
summation variables, with the final exponent at least two, or strictly
decreasing summation variables, with the first exponent at least two. This
module defines the increasing presentation and proves that reversing both the
exponent index and the summation tuple identifies it with `strictValue`.

## Main definitions

* `Index.reverse` reverses the exponent index.
* `Index.IsIncreasingAdmissible` expresses admissibility in the increasing convention.
* `StrictIncreasingTuple` is a strictly increasing tuple of positive naturals.
* `increasingSummand` and `increasingValue` give the increasing presentation.
* `increasingEquivDecreasing` reverses an increasing tuple.

## Main results

* `Index.isIncreasingAdmissible_iff_reverse_isAdmissible` transports admissibility.
* `increasingSummand_eq_strictSummand_reverse` identifies individual summands.
* `increasingValue_eq_strictValue_reverse` identifies the two series.

## References

* [K.-W. Chen et al., *Some Symmetry and Duality Theorems on Multiple
  Zeta(-star) Values*](https://arxiv.org/abs/2304.08722)
* [N. Tamang and P. Sarkar, *An algebraic proof of the duality of multiple
  zeta-star values of height one*](https://arxiv.org/abs/2307.09867)
* [Z. Li, Z. Wang, and L. Zhang, *A proof of a weighted sum conjecture for
  finite multiple zeta values of level two*](https://arxiv.org/abs/2608.10675)
* [H. Bachmann and Risan, *Formal finite multiple zeta
  values*](https://arxiv.org/abs/2608.15480)
-/


namespace MetaMathlibExt.MultipleZeta

/-- Admissibility in the increasing convention: the last exponent is at least two.
This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
def Index.IsIncreasingAdmissible (index : Index) : Prop :=
  MetaMathlibExt.MultipleZeta.IsAdmissible index.entries.reverse

/-- The reciprocal-product summand in the increasing convention.
This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
noncomputable def increasingSummand (index : Index)
    (m : StrictIncreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

/-- The multiple-zeta series in the increasing convention.
This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
@[nolint unusedArguments]
noncomputable def increasingValue (index : Index)
    (_h : index.IsIncreasingAdmissible) : ℝ :=
  ∑' m : StrictIncreasingTuple index.depth, increasingSummand index m

/-- Reversing coordinates identifies increasing tuples for an index with
decreasing tuples for its reversed index. -/
def increasingEquivDecreasing (index : Index) :
    StrictIncreasingTuple index.depth ≃
      StrictDecreasingTuple index.reverse.depth where
  toFun m :=
    ⟨fun i => m.1 (Fin.rev (Fin.castOrderIso index.reverse_depth i)), by
      intro i j hij
      have hcast :
          Fin.castOrderIso index.reverse_depth i <
            Fin.castOrderIso index.reverse_depth j := by
        simpa using hij
      exact m.2 (Fin.rev_lt_rev.mpr hcast)⟩
  invFun m :=
    ⟨fun i => m.1 (Fin.castOrderIso index.reverse_depth.symm (Fin.rev i)), by
      intro i j hij
      have hcast :
          Fin.castOrderIso index.reverse_depth.symm (Fin.rev j) <
            Fin.castOrderIso index.reverse_depth.symm (Fin.rev i) := by
        simpa using Fin.rev_lt_rev.mpr hij
      exact m.2 hcast⟩
  left_inv m := by
    ext i
    simp
  right_inv m := by
    ext i
    simp

end MetaMathlibExt.MultipleZeta
