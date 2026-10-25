/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NormalNumberSequence.lean -/


import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Def.NumberTheory.NormalNumberSequence
import Lemma.Nat.NormalNumberSequence


namespace MetaMathlibExt

example (a : ℤ) : normalSeqFib a 3 = a ^ 2 + 1 := by
  simp [normalSeqFib, normalSeq]
  ring

example (a : ℤ) :
    normalSeqFib a 5 = normalSeqFib a 3 ^ 2 + normalSeqFib a 2 ^ 2 := by
  simpa using normalSeq_odd_identity a 3 (by omega)

end MetaMathlibExt
