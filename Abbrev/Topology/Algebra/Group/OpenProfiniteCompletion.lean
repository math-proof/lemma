/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean -/

import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
open CategoryTheory
open scoped Pointwise

universe u

/-!
# Open profinite completion from open finite-index normal subgroups.

Corrects the source formalization: an open subgroup of an arbitrary
topological group need not have finite index. We index by open *and*
finite-index normal subgroups.
-/


namespace ProfiniteGrp.OpenProfiniteCompletion

/-- Open finite-index normal subgroups of `G`, the index category. -/
abbrev Index (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : FiniteIndexNormalSubgroup G // IsOpen (H : Set G) }

end ProfiniteGrp.OpenProfiniteCompletion
