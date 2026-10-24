/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Recurrences/PrimitiveDivisor.lean -/


import Mathlib.Tactic
import sympy.atlas.NumberTheory.Recurrences.PrimitiveDivisor
import Lemma.Nat.Recurrences.PrimitiveDivisor


namespace LucasSequenceTest

open LucasSequence

def sampleSequence (k : ℕ) : ℤ :=
  if k = 3 then 7 else 1

def firstTermSequence (k : ℕ) : ℤ :=
  if k = 1 then 7 else 1

def zeroAtZero (k : ℕ) : ℤ :=
  if k = 0 then 0 else 1

example : IsPrimitiveDivisor sampleSequence 5 3 7 := by
  norm_num [IsPrimitiveDivisor, sampleSequence]

example : ¬IsPrimitiveDivisor sampleSequence 7 3 7 := by
  intro h
  exact h.not_dvd_discriminant (by norm_num)

example : IsPrimitiveDivisor firstTermSequence 5 1 7 := by
  norm_num [IsPrimitiveDivisor, firstTermSequence]

example : ¬IsPrimitiveDivisor zeroAtZero 5 0 7 := by
  norm_num [IsPrimitiveDivisor]

example (h : IsPrimitiveDivisor sampleSequence 5 3 7) : Nat.Prime 7 :=
  h.prime

example (h : IsPrimitiveDivisor sampleSequence 5 3 7) : 0 < 3 :=
  h.pos

example (h : IsPrimitiveDivisor sampleSequence 5 3 7) : (7 : ℤ) ∣ sampleSequence 3 :=
  h.dvd_term

example (h : IsPrimitiveDivisor sampleSequence 5 3 7) :
    ¬(7 : ℤ) ∣ 5 * ∏ k ∈ Finset.Ico 1 3, sampleSequence k :=
  h.not_dvd_badPart

example (h : IsPrimitiveDivisor sampleSequence 5 3 7) : ¬(7 : ℤ) ∣ sampleSequence 2 :=
  h.not_dvd_prior (by decide)

end LucasSequenceTest
