/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean -/

import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Theorem.Topology.Algebra.Group.OpenProfiniteCompletion
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

/-- Canonical continuous monoid hom into the completion. -/
def eta (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : G →ₜ* completion G where
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := etaFn_continuous G

end ProfiniteGrp.OpenProfiniteCompletion
