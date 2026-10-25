/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/IsogenyVolcano.lean -/


import Instance.Combinatorics.IsogenyVolcano.Part2
import Lemma.Finset.IsogenyVolcano
import Mathlib.Tactic.FinCases
set_option autoImplicit false


def singletonLoopGraph : Multigraph Unit where
  edgeMult := fun _ _ => 2
  symm := fun _ _ => rfl

def singletonLoopVolcano : IsogenyVolcano 2 where
  prime := by decide
  V := Unit
  instFintype := inferInstance
  instDecEq := inferInstance
  graph := singletonLoopGraph
  depth := 0
  level := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
  level_surj := by
    intro i
    refine ⟨(), Fin.ext ?_⟩
    exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)).symm
  surfaceDegree := 2
  surfaceDegree_le := by decide
  surface_regular := by
    intro v _
    simp [Multigraph.degreeOn, singletonLoopGraph]
  unique_parent := by
    intro v h
    simp at h
  edges_between_levels := by
    intro v w _
    exact Or.inl ⟨rfl, rfl⟩
  degree_eq := by
    intro v h
    simp at h
  connected := by
    intro v w
    cases v
    cases w
    exact Multigraph.connected_refl singletonLoopGraph ()

