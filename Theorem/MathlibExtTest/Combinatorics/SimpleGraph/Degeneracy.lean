/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Degeneracy.lean -/


import Def.Combinatorics.SimpleGraph.Degeneracy
import Lemma.SimpleGraph.Degeneracy


namespace SimpleGraph

example {V : Type*} [Finite V] (U : Set V) : (⊥ : SimpleGraph V).IsDegenerateOn U 0 := by
  intro W hWne _
  obtain ⟨v, hvW⟩ := hWne
  refine ⟨v, hvW, ?_⟩
  simp

example {V : Type*} [Finite V] {G : SimpleGraph V} {U : Set V} {k l : ℕ}
    (h : G.IsDegenerateOn U k) (hkl : k ≤ l) : G.IsDegenerateOn U l :=
  h.mono hkl

example {V : Type*} [Finite V] {G : SimpleGraph V} {U : Set V} {k : ℕ}
    (h : G.IsDegenerate k) : G.IsDegenerateOn U k :=
  h.isDegenerateOn U

end SimpleGraph
