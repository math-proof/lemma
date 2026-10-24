/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SCullenNumber.lean -/


import sympy.atlas.NumberTheory.SCullenNumber


example : MetaMathlibExt.sCullenNumber 2 1 = 3 := rfl
example : MetaMathlibExt.sCullenNumber 2 2 = 9 := rfl
example : MetaMathlibExt.sCullenNumber 3 2 = 19 := rfl

example : MetaMathlibExt.IsSCullenNumber 2 3 := by
  refine ⟨by decide, 1, by decide, ?_⟩
  rfl

example : ¬ MetaMathlibExt.IsSCullenNumber 1 2 := by
  simp [MetaMathlibExt.IsSCullenNumber]

#print axioms MetaMathlibExt.sCullenNumber
#print axioms MetaMathlibExt.IsSCullenNumber
