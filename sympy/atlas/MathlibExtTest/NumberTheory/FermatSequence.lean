/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FermatSequence.lean -/


import sympy.atlas.NumberTheory.FermatSequence

namespace MetaMathlibExt

example : fermatSequence (fun _ => (1 : ℂ)) 0 = 0 := by
  simp [fermatSequence]

example : fermatSequence (fun _ => (1 : ℂ)) 1 = 1 := by
  have h : Nat.divisors 1 = {1} := by decide
  simp [fermatSequence, h]

example : fermatSequence (fun _ => (1 : ℂ)) 2 = 3 := by
  have h : Nat.divisors 2 = {1, 2} := by decide
  simp [fermatSequence, h, Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide)]
  norm_num

example : fermatSequence (fun m => (m : ℂ)) 2 = 5 := by
  have h : Nat.divisors 2 = {1, 2} := by decide
  simp [fermatSequence, h, Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide)]
  norm_num

example : fermatSequence (fun m => (m : ℂ)) 3 = 10 := by
  have h : Nat.divisors 3 = {1, 3} := by decide
  simp [fermatSequence, h, Finset.sum_pair (show (1 : ℕ) ≠ 3 by decide)]
  norm_num

end MetaMathlibExt
