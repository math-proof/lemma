/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Circumference.lean -/
module

public import Theorem.Combinatorics.SimpleGraph.Circumference.Part2
public import Theorem.SimpleGraph.Circumference
open SimpleGraph

public section

-- Normal API use: cycle-length sets accept a graph.
noncomputable example (G : SimpleGraph (Fin 5)) : Set ℕ :=
  G.cycleLengths

noncomputable example (G : SimpleGraph (Fin 5)) : Set ℕ :=
  G.oddCycleLengths

-- Membership uses the public characteristic lemma.
example (G : SimpleGraph (Fin 5)) (m : ℕ) :
    m ∈ G.cycleLengths ↔
      ∃ (a : Fin 5) (w : G.Walk a a), w.IsCycle ∧ w.length = m :=
  mem_cycleLengths

example (G : SimpleGraph (Fin 5)) (m : ℕ) :
    m ∈ G.oddCycleLengths ↔ m ∈ G.cycleLengths ∧ Odd m :=
  mem_oddCycleLengths

-- Semantic check: odd cycle lengths are cycle lengths.
example (G : SimpleGraph (Fin 5)) :
    G.oddCycleLengths ⊆ G.cycleLengths :=
  fun _ h => (mem_oddCycleLengths.mp h).1

