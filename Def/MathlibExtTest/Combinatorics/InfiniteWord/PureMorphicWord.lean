/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/PureMorphicWord.lean -/

module

public import Mathlib.Tactic
public import Def.Combinatorics.InfiniteWord.PureMorphicWord
public import Theorem.Finset.InfiniteWord.PureMorphicWord

@[expose] public section

namespace MetaMathlibExt

def probeMorphism : Bool → List Bool
  | false => [false, true]
  | true => [true]

end MetaMathlibExt
