/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ConsecutivePrime.lean -/


import sympy.atlas.NumberTheory.ConsecutivePrime
import Mathlib.Tactic.NormNum.Prime
import Lean.Elab.Tactic.Omega


open MetaMathlibExt

example : AreConsecutivePrimes 2 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r _hr
  omega

example : ¬ AreConsecutivePrimes 3 7 := by
  intro h
  have h5 := h.2.2.2 5 (by norm_num)
  omega

example : IsConsecutivePrimeBlock [2, 3] := by
  have h23 : AreConsecutivePrimes 2 3 := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    intro r _hr
    omega
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro p hp
    have hp' : p = 2 ∨ p = 3 := by simpa using hp
    rcases hp' with rfl | rfl <;> norm_num
  · intro x hx
    change x ∈ [(2, 3)] at hx
    have : x = (2, 3) := by simpa using hx
    subst x
    exact h23

example : IsRestrictedConsecutivePrimeBlock (fun p ↦ p ≤ 3) [2, 3] := by
  have hblock : IsConsecutivePrimeBlock [2, 3] := by
    have h23 : AreConsecutivePrimes 2 3 := by
      refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
      intro r _hr
      omega
    refine ⟨by simp, ?_, by simp, ?_⟩
    · intro p hp
      have hp' : p = 2 ∨ p = 3 := by simpa using hp
      rcases hp' with rfl | rfl <;> norm_num
    · intro x hx
      change x ∈ [(2, 3)] at hx
      have : x = (2, 3) := by simpa using hx
      subst x
      exact h23
  refine ⟨hblock, ?_⟩
  intro p hp
  have hp' : p = 2 ∨ p = 3 := by simpa using hp
  rcases hp' with rfl | rfl <;> omega

#print axioms MetaMathlibExt.AreConsecutivePrimes
#print axioms MetaMathlibExt.IsConsecutivePrimeBlock
#print axioms MetaMathlibExt.IsRestrictedConsecutivePrimeBlock
