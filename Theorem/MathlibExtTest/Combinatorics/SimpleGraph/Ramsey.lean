/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Ramsey.lean -/


import Def.Combinatorics.SimpleGraph.Ramsey
import Lemma.SimpleGraph.Ramsey


namespace SimpleGraph

/-- The arbitrary-graph API unfolds to the expected two-color containment threshold. -/
example {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    graphPairRamsey G H =
      sInf {N : ℕ | ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ} :=
  graphPairRamsey_eq_sInf G H

/-- The diagonal arbitrary-graph API specializes both colors to the same graph. -/
example {α : Type*} [Fintype α] (G : SimpleGraph α) :
    diagonalGraphRamsey G = graphPairRamsey G G :=
  rfl

/-- The shared predicate unfolds to ordinary clique containment in the two colors. -/
example (s t N : ℕ) : classicalRamsey s t N ↔
    ∀ G : SimpleGraph (Fin N),
      IsContained (completeGraph (Fin s)) G ∨
        IsContained (completeGraph (Fin t)) Gᶜ :=
  Iff.rfl

/-- Ramsey size linearity unfolds to a linear edge-count bound. -/
example {α : Type*} [Fintype α] (G : SimpleGraph α) :
    IsRamseySizeLinear G ↔
      ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        (∀ v, 0 < H.degree v) →
        (graphPairRamsey G H : ℝ) ≤ c * H.edgeSet.ncard :=
  Iff.rfl

/-- The off-diagonal Ramsey number is the infimum of the shared predicate. -/
example (s t : ℕ) :
    graphRamsey s t = sInf {N : ℕ | classicalRamsey s t N} :=
  graphRamsey_eq_sInf s t

/-- Diagonal Ramsey numbers reuse the same two-parameter API. -/
example (k : ℕ) :
    graphRamsey k k = sInf {N : ℕ |
      ∀ G : SimpleGraph (Fin N),
        IsContained (completeGraph (Fin k)) G ∨
          IsContained (completeGraph (Fin k)) Gᶜ} :=
  rfl

end SimpleGraph
