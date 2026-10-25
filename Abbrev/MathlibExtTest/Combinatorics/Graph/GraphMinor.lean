/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/GraphMinor.lean -/


import Def.Combinatorics.Graph.GraphMinor
import Lemma.Finset.Graph.GraphMinor
import Theorem.MathlibExtTest.Combinatorics.Graph.GraphMinor


namespace MathlibExtTest.Combinatorics.Graph.GraphMinor

abbrev emptyBool : MetaMathlibExt.FinGraph where
  V := Bool
  G := ⊥

abbrev completeBool : MetaMathlibExt.FinGraph where
  V := Bool
  G := ⊤

abbrev emptyUnit : MetaMathlibExt.FinGraph where
  V := Unit
  G := ⊥

abbrev unitToTrue : Unit ↪ Bool where
  toFun _ := true
  inj' _ _ _ := Subsingleton.elim _ _

end MathlibExtTest.Combinatorics.Graph.GraphMinor
