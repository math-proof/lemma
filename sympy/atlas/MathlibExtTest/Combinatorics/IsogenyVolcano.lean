/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/IsogenyVolcano.lean -/


import sympy.atlas.Combinatorics.IsogenyVolcano
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

example : singletonLoopVolcano.isSurface () := rfl
example : singletonLoopVolcano.isFloor () := rfl
example : singletonLoopVolcano.graph.degree () = 2 := by
  change Finset.sum Finset.univ (fun _ : Unit => 2) = 2
  simp
example : singletonLoopVolcano.IsHorizontalEdge () () := by
  refine ⟨?_, rfl, rfl⟩
  decide
example :
    singletonLoopVolcano.IsHorizontalEdge () () ∨
      singletonLoopVolcano.IsDescendingEdge () () ∨
        singletonLoopVolcano.IsAscendingEdge () () := by
  apply IsogenyVolcano.edge_direction (C := singletonLoopVolcano) () ()
  decide

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

example : depthOneVolcano.isSurface false := rfl
example : depthOneVolcano.isFloor true := rfl
example : depthOneVolcano.IsDescendingEdge false true := by
  refine ⟨?_, rfl⟩
  decide
example : depthOneVolcano.IsAscendingEdge true false := by
  refine ⟨?_, rfl⟩
  decide
example :
    depthOneVolcano.IsDescendingEdge false true ↔
      depthOneVolcano.IsAscendingEdge true false :=
  IsogenyVolcano.descending_iff_ascending_symm
    (C := depthOneVolcano) false true
example :
    depthOneVolcano.IsHorizontalEdge false true ∨
      depthOneVolcano.IsDescendingEdge false true ∨
        depthOneVolcano.IsAscendingEdge false true := by
  apply IsogenyVolcano.edge_direction (C := depthOneVolcano) false true
  decide
