/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean -/

import Mathlib.Topology.Separation.Hausdorff

/-!
# Inverse limits of spaces over a preorder

This module formalizes the concrete inverse limit from ATLAS NumberTheoryI
Definition 8.9: for a family `X` of spaces indexed by a preorder and
transition maps `f h : X j → X i` for `h : i ≤ j`, the inverse limit is the
set of compatible dependent functions, that is, tuples `x` satisfying
`f h (x j) = x i` for every `h : i ≤ j`.

It also formalizes the topological half of Proposition 8.10: the limit set is
closed when every factor is Hausdorff and every transition map is continuous,
and hence compact when every factor is compact.

## Main definitions

* `InverseLimit.carrier`: the set of compatible tuples.

## Main results

* `InverseLimit.proj_compat`: elements of the limit project compatibly.
* `InverseLimit.isClosed_carrier`: the limit set is closed in the product.
* `InverseLimit.isCompact_carrier`: the limit set is compact in the product.

## References

* ATLAS NumberTheoryI, Definition 8.9 (inverse limit as compatible tuples)
  and Proposition 8.10 (closedness and compactness of the limit).
-/

namespace InverseLimit

variable {ι : Type*} [Preorder ι]
variable {X : ι → Type*}

/-- The concrete inverse limit from ATLAS NumberTheoryI Definition 8.9: the set
of dependent functions `x : ∀ i, X i` compatible with the transition maps,
that is, `f h (x j) = x i` whenever `h : i ≤ j`. -/
def carrier (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i) : Set (∀ i, X i) :=
  { x | ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i }
end InverseLimit
