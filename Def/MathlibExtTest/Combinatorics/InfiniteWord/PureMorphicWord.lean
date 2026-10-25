/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean -/


import Mathlib.Tactic
import Def.Combinatorics.InfiniteWord.PureMorphicWord
import Lemma.Finset.InfiniteWord.PureMorphicWord


namespace MetaMathlibExt

def probeMorphism : Bool → List Bool
  | false => [false, true]
  | true => [true]

end MetaMathlibExt
