/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/LinearPartition.lean -/


import sympy.atlas.Combinatorics.LinearPartition
import Lemma.Finset.LinearPartition
import Mathlib.Tactic

namespace MetaMathlibExt

private def graph02 : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun a b => a = 0 ∧ b = 2

private instance : DecidableRel graph02.Adj := fun a b => by
  simp only [graph02, SimpleGraph.fromRel_adj]
  infer_instance

/-- The sole edge joins the nonconsecutive endpoints of `[0, 1, 2]`. -/
example : graph02.Adj 0 2 := by
  simp [graph02]

/-- A block may contain adjacent graph vertices when they are not consecutive in the list. -/
example : LinearPartition graph02 1 where
  blocks := ({([0, 1, 2] : List (Fin 3))} : Finset (List (Fin 3)))
  card_eq := by simp
  nonempty := by
    intro L hL
    rw [Finset.mem_singleton] at hL
    subst L
    simp
  nodup := by
    intro L hL
    rw [Finset.mem_singleton] at hL
    subst L
    decide
  covers := by
    intro v
    refine ⟨[0, 1, 2], ?_, ?_⟩
    · constructor
      · simp
      · fin_cases v <;> simp
    · intro L hL
      exact Finset.mem_singleton.mp hL.1
  consecutive := by
    intro L hL
    rw [Finset.mem_singleton] at hL
    subst L
    decide

/-- The same list is invalid in a complete graph because consecutive vertices are adjacent. -/
example : ¬List.IsChain
    (fun a b => ¬(⊤ : SimpleGraph (Fin 3)).Adj a b) [0, 1, 2] := by
  decide

/-- The empty graph on the empty vertex type has the empty zero-linear partition. -/
example : LinearPartition (⊥ : SimpleGraph (Fin 0)) 0 where
  blocks := ∅
  card_eq := by simp
  nonempty := by simp
  nodup := by simp
  covers := by
    intro v
    exact Fin.elim0 v
  consecutive := by simp

end MetaMathlibExt
