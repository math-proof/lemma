/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PartialBellPolynomial.lean -/
module

public import Mathlib.Tactic
public import Def.Combinatorics.Enumerative.PartialBellPolynomial

public section

namespace MetaMathlibExt

example : partialBellPolynomial 0 0 (fun _ => (1 : ℕ)) = 1 := by decide

example : partialBellPolynomial 3 2 (fun _ => (1 : ℕ)) = 3 := by decide

end MetaMathlibExt
