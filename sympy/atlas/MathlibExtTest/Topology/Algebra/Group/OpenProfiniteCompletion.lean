/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/Group/OpenProfiniteCompletion.lean -/


import sympy.atlas.Topology.Algebra.Group.OpenProfiniteCompletion
import Lemma.Set.Algebra.Group.OpenProfiniteCompletion


open ProfiniteGrp.OpenProfiniteCompletion

universe u

section GenericTop
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def topIndex : Index G :=
  ⟨FiniteIndexNormalSubgroup.ofSubgroup (⊤ : Subgroup G), isOpen_univ⟩

example : FiniteGrp.{u} := (finiteGrpDiagram G).obj (topIndex G)

example : ProfiniteGrp.{u} := (diagram G).obj (topIndex G)

example : ProfiniteGrp.{u} := completion G

example (x : G) :
    ((etaFn G x).val (topIndex G) : G ⧸ (topIndex G).1.toSubgroup) =
    QuotientGroup.mk x :=
  etaFn_apply G x (topIndex G)

example : Index G := topIndex G

example : FiniteGrp.{u} := (finiteGrpDiagram G).obj (topIndex G)

example : Continuous (eta G) ∧ DenseRange (eta G) :=
  continuous_eta_denseRange G

end FiniteDiscrete

section InfiniteDiscrete
-- Model case: `Multiplicative ℤ` with discrete topology; stated generically
-- so the corrected construction and density elaborate with no compactness.
variable (H : Type u) [Group H] [TopologicalSpace H] [DiscreteTopology H]
  [IsTopologicalGroup H] [Infinite H]

example : Index H := topIndex H

example : Infinite H := inferInstance

example : Continuous (eta H) ∧ DenseRange (eta H) :=
  continuous_eta_denseRange H

end InfiniteDiscrete
