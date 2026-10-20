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

/-- Membership in the inverse limit is exactly the compatibility condition. -/
@[simp]
theorem mem_carrier_iff {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    {x : ∀ i, X i} :
    x ∈ carrier f ↔ ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i :=
  Iff.rfl

/-- Projection compatibility for limit elements: applying a transition map to
a higher component agrees with the lower component. -/
theorem proj_compat {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    {x : ∀ i, X i} (hx : x ∈ carrier f) ⦃i j : ι⦄ (h : i ≤ j) :
    f h (x j) = x i :=
  hx h

variable [∀ i, TopologicalSpace (X i)]

/-- The inverse limit set is closed in the product when every factor is
Hausdorff and every transition map is continuous. Each compatibility equation
`f h (x j) = x i` cuts out a closed set by `isClosed_eq`, and the limit is the
intersection of all of them. -/
theorem isClosed_carrier [∀ i, T2Space (X i)]
    {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
    IsClosed (carrier f) := by
  have heq : carrier f =
      ⋂ (i : ι) (j : ι) (h : i ≤ j), { x | f h (x j) = x i } := by
    ext x
    simp [carrier]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h =>
    isClosed_eq ((hf h).comp (continuous_apply j)) (continuous_apply i)

/-- The inverse limit set is compact in the product when every factor is
compact Hausdorff and every transition map is continuous: it is a closed
subset of a compact product. -/
theorem isCompact_carrier [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
    {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
    (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
    IsCompact (carrier f) :=
  (isClosed_carrier hf).isCompact

end InverseLimit
