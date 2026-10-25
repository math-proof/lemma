/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PerrinSequence.lean -/


import Def.NumberTheory.PerrinSequence


namespace MetaMathlibExt

example : perrinSequence 0 = 3 := rfl

example : perrinSequence 1 = 0 := rfl

example : perrinSequence 2 = 2 := rfl

example : perrinSequence 3 = 3 := rfl

example : perrinSequence 4 = 2 := rfl

example : perrinSequence 5 = 5 := rfl

end MetaMathlibExt
