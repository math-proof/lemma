/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Contraction.lean -/


import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
import Lemma.SimpleGraph.Contraction
import Def.MathlibExtTest.Combinatorics.SimpleGraph.Contraction


namespace MathlibExtTest.Combinatorics.SimpleGraph.Contraction

example : SimpleGraph.collapseOutside retained 1 = some one := by
  exact SimpleGraph.collapseOutside_of_mem retained (by simp [retained])

example : SimpleGraph.collapseOutside retained 3 = none := by
  exact SimpleGraph.collapseOutside_of_notMem retained (by simp [retained])

example : SimpleGraph.collapseOutside retained 1 ≠ some zero := by
  intro h
  have hval := congrArg Fin.val
    (SimpleGraph.collapseOutside_eq_some_iff retained 1 zero |>.mp h)
  change 1 = 0 at hval
  omega

example : SimpleGraph.collapseOutside retained 0 ≠ none := by
  intro h
  have hout := SimpleGraph.collapseOutside_eq_none_iff retained 0 |>.mp h
  exact hout (by simp [retained])

example : ∃ v : Fin 4, SimpleGraph.collapseOutside retained v = none := by
  exact SimpleGraph.collapseOutside_surjective
    (D := retained) ⟨2, by simp [retained]⟩ none

example : ((⊤ : SimpleGraph (Fin 4)).contractOutside retained).Adj
    (some zero) (some one) := by
  rw [SimpleGraph.contractOutside_adj_some]
  simp [zero, one]

example : ((⊤ : SimpleGraph (Fin 4)).contractOutside retained).Adj
    (some zero) none := by
  rw [SimpleGraph.contractOutside_adj_none]
  exact ⟨2, by simp [retained], by simp [zero]⟩

example : 2 < Fintype.card (Option retained) := by
  have hconnected : ((⊤ : SimpleGraph (Fin 4)).induce retained).Connected := by
    rw [SimpleGraph.induce_top]
    let _ : Nonempty retained := ⟨zero⟩
    exact SimpleGraph.connected_top
  have hout : retainedᶜ.Nonempty := ⟨2, by simp [retained]⟩
  have hcontract := completeGraph_isVertexConnected_two.contractOutside
    (D := retained) (by simp [retained]) hconnected hout
  exact hcontract.card_gt

example : Fintype.card (Option retained) < Fintype.card (Fin 4) := by
  apply SimpleGraph.card_contractOutside_lt retained
  rw [Fintype.card_compl_set]
  simp [retained]

end MathlibExtTest.Combinatorics.SimpleGraph.Contraction
