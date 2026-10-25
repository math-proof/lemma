/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/HamiltonianCycle.lean -/


import Lemma.SimpleGraph.HamiltonianCycle


namespace MathlibExtTest.Combinatorics.SimpleGraph.HamiltonianCycle

-- The cyclic listing `0, 1, 2, 0` witnesses a Hamiltonian cycle in the complete graph.
example : (⊤ : SimpleGraph (Fin 3)).IsHamiltonian := by
  apply SimpleGraph.IsHamiltonian.of_cyclic_list (⊤ : SimpleGraph (Fin 3))
    [0, 1, 2, 0] (by decide)
  · decide
  · decide
  · decide
  · decide
  · decide

end MathlibExtTest.Combinatorics.SimpleGraph.HamiltonianCycle
