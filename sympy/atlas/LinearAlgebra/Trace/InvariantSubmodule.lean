/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Trace/InvariantSubmodule.lean -/

/-
Author: Muse Code
-/

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Trace additivity for an invariant submodule

For an endomorphism `e` of a finite-dimensional vector space `V` over a field
that preserves a submodule `W`, the trace of `e` is the sum of the trace of the
restriction to `W` and the trace of the induced map on the quotient `V ⧸ W`.

This is the trace analogue of `LinearMap.det_eq_det_mul_det`; the proof follows
the same block-basis pattern via `Module.Basis.sumQuot`.

ATLAS source and scope: this module is a prerequisite stage for ATLAS item
NumberTheoryI N261 (Theorem 12.27), whose different-valuation target is
defined and stated in
`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines 1237-1324, at
revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`
(<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324>).
Those ATLAS lines define and state the different-valuation target but do not
state these generic trace-additivity lemmas. Source-to-API map:
`LinearMap.trace_eq_trace_restrict_add_trace_mapQ`,
`LinearMap.trace_eq_trace_restrict_ker_add_of_surjective` are generic
prerequisites intended for the future step of iterating the trace across the
maximal-ideal quotient filtration.
This module is a prerequisite stage only, not the full N261 theorem: it proves
no different-ideal containment and no valuation bound. The ATLAS statement
`different_valuation_exact` (lines 1269-1276 there) is unfinished and false in
general wild ramification, so it is neither copied nor used here.
-/

open Module.Basis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
