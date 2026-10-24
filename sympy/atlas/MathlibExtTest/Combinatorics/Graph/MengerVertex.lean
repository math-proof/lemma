/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/MengerVertex.lean -/


import sympy.atlas.Combinatorics.Graph.MengerVertex
import Lemma.Finset.Graph.MengerVertex

namespace MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

/-- Client check: the walk-separator characterization of `IsSTVertexCut` is public
and has the expected statement. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (C : Finset V) :
    IsSTVertexCut G s t C ↔
      s ∉ C ∧ t ∉ C ∧ ∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C :=
  isSTVertexCut_iff_walkSeparator G s t C

/-- Client check: the forward direction turns a cut into a walk-hitting set. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (C : Finset V)
    (hcut : IsSTVertexCut G s t C) (p : G.Walk s t) :
    ∃ v ∈ p.support, v ∈ C := by
  obtain ⟨-, _, hhit⟩ := (isSTVertexCut_iff_walkSeparator G s t C).mp hcut
  exact hhit p

end MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted
