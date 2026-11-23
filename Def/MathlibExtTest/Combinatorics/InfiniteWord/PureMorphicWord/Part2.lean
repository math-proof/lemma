/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean -/

module

public import Mathlib.Tactic
public import Def.Combinatorics.InfiniteWord.PureMorphicWord
public import Theorem.Finset.InfiniteWord.PureMorphicWord
public import Theorem.MathlibExtTest.Combinatorics.InfiniteWord.PureMorphicWord

@[expose] public section

namespace MetaMathlibExt

def doublingUnitMorphism (_ : Unit) : List Unit := [(), ()]

def constantUnitWord (_ : Nat) : Unit := ()

end MetaMathlibExt
