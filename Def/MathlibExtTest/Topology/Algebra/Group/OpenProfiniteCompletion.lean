/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/Group/OpenProfiniteCompletion.lean -/

module

public import Def.Topology.Algebra.Group.OpenProfiniteCompletion.Part2
public import Theorem.Set.Algebra.Group.OpenProfiniteCompletion

@[expose] public section

open ProfiniteGrp.OpenProfiniteCompletion

universe u


section GenericTop

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def topIndex : Index G :=
  ⟨FiniteIndexNormalSubgroup.ofSubgroup (⊤ : Subgroup G), isOpen_univ⟩

end GenericTop
