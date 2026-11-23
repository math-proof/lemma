/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/FibonacciWord.lean -/
module

public import Theorem.Combinatorics.InfiniteWord.FibonacciWord
public import Theorem.Finset.InfiniteWord.FibonacciWord

public section

namespace MetaMathlibExt

example : fibWord 4 =
    [false, true, false, false, true, false, true, false] := rfl

example : (List.range 8).map fibInf =
    [false, true, false, false, true, false, true, false] := by
  decide

end MetaMathlibExt
