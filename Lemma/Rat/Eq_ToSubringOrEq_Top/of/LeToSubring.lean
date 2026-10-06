import Mathlib
import sympy.Basic


/--
[ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing.lean)
-/
@[main]
private lemma main
  [Field K]
  {A : ValuationSubring K} [IsDiscreteValuationRing ↥A]
  {B : Subring K}
-- given
  (h : A.toSubring ≤ B) :
-- imply
  B = A.toSubring ∨ B = ⊤ := by
-- proof
  classical
  let B' : ValuationSubring K := ValuationSubring.ofLE A B h
  have hB' : (B' : ValuationSubring K).toSubring = B := rfl
  have hAB' : A ≤ B' := fun x hx => h hx

  set P : Ideal ↥A := A.idealOfLE B' hAB' with hP
  have hPB' : A.ofPrime P = B' := ValuationSubring.ofPrime_idealOfLE A B' hAB'
  by_cases hbot : P = ⊥
  · right
    rw [← hB', ← hPB']
    have : A.ofPrime P = ⊤ := by
      haveI : (⊥ : Ideal ↥A).IsPrime := Ideal.bot_prime
      have e : A.ofPrime P = A.ofPrime ⊥ := by congr 1
      rw [e]; exact ValuationSubring.ofPrime_bot A
    rw [this]; rfl
  · left
    rw [← hB', ← hPB']
    have hmax : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    have hPm : P = IsLocalRing.maximalIdeal ↥A := IsLocalRing.eq_maximalIdeal hmax
    have : A.ofPrime P = A := by
      have e : A.ofPrime P = A.ofPrime (IsLocalRing.maximalIdeal ↥A) := by congr 1
      rw [e]; exact ValuationSubring.ofPrime_top A
    rw [this]


-- created on 2026-10-05
