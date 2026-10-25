/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/StrongSquareCycle.lean -/


import Def.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle


namespace MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle

theorem adj_zero_one :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 0 1 :=
  ⟨by decide, Or.inl (by simp)⟩

theorem adj_one_two :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 1 2 :=
  ⟨by decide, Or.inl (by simp)⟩

theorem adj_two_zero :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 2 0 :=
  ⟨by decide, Or.inl (by simp)⟩

end MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle
