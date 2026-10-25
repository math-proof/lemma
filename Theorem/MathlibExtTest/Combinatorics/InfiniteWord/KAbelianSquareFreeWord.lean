/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/KAbelianSquareFreeWord.lean -/


import Def.Combinatorics.InfiniteWord.KAbelianSquareFreeWord


namespace MetaMathlibExt

example : wordFactorCount ([0, 0, 0] : List ℕ) [0, 0] = 2 := by decide

example : wordFactorCount ([0, 1, 0] : List ℕ) [0] = 2 := by decide

example : wordFactorCount ([0, 1] : List ℕ) [] = 0 := by decide

end MetaMathlibExt
