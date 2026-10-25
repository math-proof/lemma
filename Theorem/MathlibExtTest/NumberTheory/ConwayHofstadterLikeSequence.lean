/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ConwayHofstadterLikeSequence.lean -/


import Def.NumberTheory.ConwayHofstadterLikeSequence
import Mathlib.Tactic


namespace MetaMathlibExt

example : conwayHofstadterResidue 6 3 = 3 := by
  decide

example : conwayHofstadterResidue 7 3 = 1 := by
  decide

example {c : ℕ → ℕ} (h : IsConwayHofstadterLikeSequence 2 c) : c 3 = 2 := by
  simpa [conwayHofstadterResidue, h.1, h.2.1] using h.2.2 3 (by omega)

#print axioms conwayHofstadterResidue
#print axioms IsConwayHofstadterLikeSequence

end MetaMathlibExt
