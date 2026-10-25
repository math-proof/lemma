/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/Complexity.lean -/


import Def.Computability.Complexity.Part3
import Lemma.Nat.Complexity


namespace MetaMathlibExt

open BitstringEncoding

example (b : Bool) : bitDecode (bitEncode b) = some b := by simp

example (p : Bool × Bool) : bitDecode (bitEncode p) = some p := by simp

example (l : List Bool) : bitDecode (bitEncode l) = some l := by simp

example (l rest : List Bool) : undelimit (delimit l ++ rest) = some (l, rest) := by simp

example : undelimit [true] = none := rfl

example : undelimitBlocks [true, false] = none := rfl

example (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l := by
  exact undelimitBlocks_flatten_delimit l

example : ComplexityTheory.P = {L | ComplexityTheory.IsPolyTime L} := rfl

example : ComplexityTheory.coNP = {L | Lᶜ ∈ ComplexityTheory.NP} := rfl

end MetaMathlibExt
