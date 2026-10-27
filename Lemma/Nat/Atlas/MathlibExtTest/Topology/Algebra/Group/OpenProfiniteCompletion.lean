import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Topology.Algebra.Group.OpenProfiniteCompletion
open ProfiniteGrp.OpenProfiniteCompletion


/--
[continuous_eta_denseRange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
lemma continuous_eta_denseRange
  {G : Type u}
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G] :
-- imply
  Continuous (eta G) ∧ DenseRange (eta G) :=
-- proof
  ⟨(eta G).continuous_toFun, denseRange_eta G⟩
section FiniteDiscrete
variable (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [IsTopologicalGroup G]


-- created on 2026-10-23
