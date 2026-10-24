/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/FibonacciWord.lean -/


import sympy.atlas.Combinatorics.InfiniteWord.FibonacciWord
import Lemma.Finset.InfiniteWord.FibonacciWord

namespace MetaMathlibExt

example : fibWord 4 =
    [false, true, false, false, true, false, true, false] := rfl

example : (List.range 8).map fibInf =
    [false, true, false, false, true, false, true, false] := by
  decide

end MetaMathlibExt
