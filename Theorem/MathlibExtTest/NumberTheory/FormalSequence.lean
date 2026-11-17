/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FormalSequence.lean -/
module

public import Def.NumberTheory.FormalSequence
public import Mathlib.Tactic.NormNum

public section

namespace MetaMathlibExt

example : IsFormalSequence (fun _ => (1 : ℚ)) 1 1 1 := by
  norm_num [IsFormalSequence, formalAlpha, formalBeta]

example : ¬ IsFormalSequence (fun _ => (0 : ℚ)) 0 0 0 := by
  simp [IsFormalSequence]

example : ¬ IsFormalSequence (fun n => (n : ℚ)) 0 1 2 := by
  intro h
  have hrec := h.2.2.2.2 1
  norm_num [formalAlpha, formalBeta] at hrec

end MetaMathlibExt
