/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NStepLucasSequence.lean -/


import Def.NumberTheory.NStepLucasSequence


namespace MetaMathlibExt

example : nStepLucas 2 0 = 0 := by decide

example : nStepLucas 2 1 = 1 := by decide

example : nStepLucas 2 2 = 3 := by decide

example : nStepLucas 2 3 = 4 := by decide

example : nStepLucas 2 4 = 7 := by decide

end MetaMathlibExt
