/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ConnellSequence.lean -/


import sympy.atlas.Combinatorics.Enumerative.ConnellSequence

namespace MetaMathlibExt

def connellTwoOne : ConnellParameters :=
  { m := 2, r := 1, two_le_m := by decide, pos_r := by decide }

def connellFiveThree : ConnellParameters :=
  { m := 5, r := 3, two_le_m := by decide, pos_r := by decide }

example : List.ofFn (fun i : Fin 10 ↦ connellSequence connellTwoOne i) =
    [1, 2, 4, 5, 7, 9, 10, 12, 14, 16] := by
  decide

example : List.ofFn (fun i : Fin 12 ↦ connellSequence connellFiveThree i) =
    [1, 2, 7, 12, 17, 18, 23, 28, 33, 38, 43, 48] := by
  decide

#print axioms connellRowLength
#print axioms connellRowStart
#print axioms connellEntry
#print axioms connellRowEntries
#print axioms connellSequence

end MetaMathlibExt
