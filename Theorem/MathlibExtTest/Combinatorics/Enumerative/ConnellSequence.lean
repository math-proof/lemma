/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ConnellSequence.lean -/


import Def.Combinatorics.Enumerative.ConnellSequence.Part2
import Def.MathlibExtTest.Combinatorics.Enumerative.ConnellSequence


namespace MetaMathlibExt

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
