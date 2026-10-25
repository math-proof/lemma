/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean -/


import Mathlib.Tactic
import Def.Combinatorics.InfiniteWord.PureMorphicWord
import Lemma.Finset.InfiniteWord.PureMorphicWord
import Theorem.MathlibExtTest.Combinatorics.InfiniteWord.PureMorphicWord


namespace MetaMathlibExt

def doublingUnitMorphism (_ : Unit) : List Unit := [(), ()]

def constantUnitWord (_ : Nat) : Unit := ()

end MetaMathlibExt
