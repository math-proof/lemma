/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean -/

import Def.NumberTheory.MultipleZeta.Series.Part3
import Lemma.Nat.MultipleZeta.Series
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

/-- Reverse the exponent entries of a multiple-zeta index. -/
def Index.reverse (index : Index) : Index :=
  match index with
  | ⟨n, composition⟩ => ⟨n, composition.reverse⟩

end MetaMathlibExt.MultipleZeta
