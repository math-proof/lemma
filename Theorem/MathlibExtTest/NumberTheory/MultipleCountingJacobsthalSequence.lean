/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleCountingJacobsthalSequence.lean -/


import Def.NumberTheory.MultipleCountingJacobsthalSequence


namespace MetaMathlibExt

example : multipleCountingJacobsthalSequence 2 3 0 = 0 := by decide

example : multipleCountingJacobsthalSequence 2 3 1 = 1 := by decide

example : multipleCountingJacobsthalSequence 3 5 2 = 4 := by decide

#print axioms multipleCountingJacobsthalSequence

end MetaMathlibExt
