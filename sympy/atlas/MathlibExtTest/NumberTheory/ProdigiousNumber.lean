/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ProdigiousNumber.lean -/


import sympy.atlas.NumberTheory.ProdigiousNumber

example : ¬ MetaMathlibExt.IsProdigious 0 12 := by decide

example : ¬ MetaMathlibExt.IsProdigious 1 12 := by decide

example : ¬ MetaMathlibExt.IsProdigious 10 0 := by decide

example : MetaMathlibExt.IsProdigious 2 5 := by decide

example : MetaMathlibExt.IsProdigious 10 12 := by decide

example : ¬ MetaMathlibExt.IsProdigious 10 13 := by decide
