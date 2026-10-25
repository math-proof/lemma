/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean -/

-- MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Def.Combinatorics.SimpleGraph.CenteredColoring
import Lemma.SimpleGraph.CenteredColoring
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.CenteredColoring
open SimpleGraph


/-- Constant coloring of an edgeless graph: proper since there are no edges. -/
def constColor : (⊥ : SimpleGraph (Fin 2)).Coloring (Fin 1) :=
  ⟨fun _ => 0, fun h => False.elim h⟩

