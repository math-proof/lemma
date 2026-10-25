/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Recurrences/PrimitiveDivisor.lean -/


import Mathlib.Tactic
import Def.NumberTheory.Recurrences.PrimitiveDivisor
import Lemma.Nat.Recurrences.PrimitiveDivisor


namespace LucasSequenceTest

open LucasSequence

def sampleSequence (k : ℕ) : ℤ :=
  if k = 3 then 7 else 1

def firstTermSequence (k : ℕ) : ℤ :=
  if k = 1 then 7 else 1

def zeroAtZero (k : ℕ) : ℤ :=
  if k = 0 then 0 else 1

end LucasSequenceTest
