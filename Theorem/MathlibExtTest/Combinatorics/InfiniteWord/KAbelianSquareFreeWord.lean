/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/KAbelianSquareFreeWord.lean -/
module

public import Def.Combinatorics.InfiniteWord.KAbelianSquareFreeWord

public section

namespace MetaMathlibExt

example : wordFactorCount ([0, 0, 0] : List ℕ) [0, 0] = 2 := by decide

example : wordFactorCount ([0, 1, 0] : List ℕ) [0] = 2 := by decide

example : wordFactorCount ([0, 1] : List ℕ) [] = 0 := by decide

end MetaMathlibExt
