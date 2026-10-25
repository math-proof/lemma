/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/TetranacciSequence.lean -/


import Def.NumberTheory.TetranacciSequence


namespace MetaMathlibExt

example : tetranacci 0 = 0 := rfl

example : tetranacci 1 = 0 := rfl

example : tetranacci 2 = 0 := rfl

example : tetranacci 3 = 1 := rfl

example : tetranacci 4 = 1 := rfl

example : tetranacci 5 = 2 := rfl

example : tetranacci 6 = 4 := rfl

example : tetranacci 7 = 8 := rfl

example (n : ℕ) :
    tetranacci (n + 4) =
      tetranacci (n + 3) + tetranacci (n + 2) + tetranacci (n + 1) + tetranacci n := rfl

#print axioms MetaMathlibExt.tetranacci

end MetaMathlibExt
