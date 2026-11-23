/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean -/

-- MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Def.Combinatorics.SimpleGraph.CenteredColoring
public import Theorem.SimpleGraph.CenteredColoring
public import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.CenteredColoring

@[expose] public section

open SimpleGraph


/-- Constant coloring of an edgeless graph: proper since there are no edges. -/
def constColor : (⊥ : SimpleGraph (Fin 2)).Coloring (Fin 1) :=
  ⟨fun _ => 0, fun h => False.elim h⟩

