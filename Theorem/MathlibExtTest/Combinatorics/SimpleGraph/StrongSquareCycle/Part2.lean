/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/StrongSquareCycle.lean -/


import Def.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle
import Def.MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle


namespace MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle

example :
    ∃ p : (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0, p.IsHamiltonianCycle := by
  obtain ⟨p, hp, -, -⟩ :=
    (SimpleGraph.hasStrongSquareCycle_iff (⊤ : SimpleGraph (Fin 3)) 0).mp
      complete_three_hasStrongSquareCycle
  exact ⟨p, hp⟩

end MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle
