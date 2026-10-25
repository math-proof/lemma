/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/IsogenyVolcano.lean -/


import Instance.Combinatorics.IsogenyVolcano.Part2
import Lemma.Finset.IsogenyVolcano
import Mathlib.Tactic.FinCases
import Theorem.MathlibExtTest.Combinatorics.IsogenyVolcano
set_option autoImplicit false


def depthOneGraph : Multigraph Bool where
  edgeMult
    | false, false => 2
    | false, true => 1
    | true, false => 1
    | true, true => 0
  symm := by
    intro v w
    cases v <;> cases w <;> rfl

def depthOneLevel : Bool → Fin 2
  | false => 0
  | true => 1

def depthOneVolcano : IsogenyVolcano 2 where
  prime := by decide
  V := Bool
  instFintype := inferInstance
  instDecEq := inferInstance
  graph := depthOneGraph
  depth := 1
  level := depthOneLevel
  level_surj := by
    intro i
    fin_cases i
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  surfaceDegree := 2
  surfaceDegree_le := by decide
  surface_regular := by
    intro v hv
    cases v with
    | false => decide
    | true => exact absurd hv (by decide)
  unique_parent := by
    intro v hv
    cases v with
    | false => exact absurd hv (by decide)
    | true => decide
  edges_between_levels := by
    intro v w h
    cases v <;> cases w <;>
      simp [depthOneLevel, depthOneGraph] at h ⊢
  degree_eq := by
    intro v hv
    cases v <;>
      simp [depthOneLevel, Multigraph.degree, depthOneGraph] at hv ⊢
  connected := by
    intro v w
    cases v <;> cases w
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by simp [Multigraph.Adj, depthOneGraph])
    · exact Relation.ReflTransGen.single (by simp [Multigraph.Adj, depthOneGraph])
    · exact Relation.ReflTransGen.refl

