/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedSylvester.lean -/


import sympy.atlas.NumberTheory.GeneralizedSylvester
import Lemma.Nat.GeneralizedSylvester

#check Nat.generalizedSylvester
#check Nat.generalizedSylvester_zero
#check Nat.generalizedSylvester_succ
#check Nat.generalizedSylvester_pos

example : Nat.generalizedSylvester 1 0 = 2 := by simp
example : Nat.generalizedSylvester 1 1 = 3 := by simp
example : Nat.generalizedSylvester 1 2 = 7 := by simp
example : Nat.generalizedSylvester 1 3 = 43 := by simp

example : Nat.generalizedSylvester 3 0 = 4 := by simp
example : Nat.generalizedSylvester 3 1 = 13 := by simp

example : Nat.generalizedSylvester 0 0 = 1 := by simp
example : Nat.generalizedSylvester 0 1 = 1 := by simp

example (n k : ℕ) : 0 < Nat.generalizedSylvester n k :=
  Nat.generalizedSylvester_pos n k
