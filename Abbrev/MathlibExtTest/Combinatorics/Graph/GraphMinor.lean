/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/GraphMinor.lean -/


module

public import Def.Combinatorics.Graph.GraphMinor
public import Theorem.Finset.Graph.GraphMinor
public import Theorem.MathlibExtTest.Combinatorics.Graph.GraphMinor

@[expose] public section


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
