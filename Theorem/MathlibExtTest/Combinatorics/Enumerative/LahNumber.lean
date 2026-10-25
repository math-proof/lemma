/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/LahNumber.lean -/


import Def.Combinatorics.Enumerative.LahNumber


namespace MetaMathlibExt

example : unsignedLahNumber 0 0 = 1 := rfl

example : unsignedLahNumber 0 1 = 0 := rfl

example : unsignedLahNumber 1 0 = 0 := rfl

example : unsignedLahNumber 2 3 = 0 := rfl

example : unsignedLahNumber 3 1 = 6 := rfl

example : unsignedLahNumber 3 2 = 6 := rfl

example : unsignedLahNumber 3 3 = 1 := rfl

example : unsignedLahNumber 4 1 = 24 := rfl

example : unsignedLahNumber 4 2 = 36 := rfl

example : unsignedLahNumber 4 3 = 12 := rfl

example : unsignedLahNumber 4 4 = 1 := rfl

example : signedLahNumber 3 1 = 6 := rfl

example : signedLahNumber 3 2 = -6 := rfl

example : signedLahNumber 4 1 = -24 := rfl

example : signedLahNumber 4 2 = 36 := rfl

example : signedLahNumber 4 3 = -12 := rfl

example : signedLahNumber 2 3 = 0 := rfl

#print axioms unsignedLahNumber
#print axioms signedLahNumber

end MetaMathlibExt
