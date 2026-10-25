/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean -/


import Def.Combinatorics.Enumerative.JacobiStirlingFirstKind
import Lemma.Finset.Enumerative.JacobiStirlingFirstKind
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt

example : jacobiStirlingFirst 0 0 (2 : ℝ) = 1 := by
  norm_num [jacobiStirlingFirst_initial_row]

example : jacobiStirlingFirst 0 1 (2 : ℝ) = 0 := by
  norm_num [jacobiStirlingFirst_initial_row]

example : jacobiStirlingFirst 1 1 (2 : ℝ) = 1 := by
  exact jacobiStirlingFirst_diagonal 1 (2 : ℝ)

example : jacobiStirlingFirst 2 1 (2 : ℝ) = -3 := by
  rw [jacobiStirlingFirst_recurrence 1 0 (2 : ℝ)]
  norm_num [jacobiStirlingFirst, jacobiStirlingFirstPoly, Finset.prod_range_succ]

example : jacobiStirlingFirst 2 2 (2 : ℝ) = 1 := by
  exact jacobiStirlingFirst_diagonal 2 (2 : ℝ)

example : jacobiStirlingFirst 2 3 (2 : ℝ) = 0 := by
  exact jacobiStirlingFirst_support 2 3 (2 : ℝ) (by omega)

example (n k : ℕ) (ζ : ℝ) :
    jacobiStirlingFirst (n + 1) (k + 1) ζ =
      jacobiStirlingFirst n k ζ -
        (n : ℝ) * ((n : ℝ) + ζ) * jacobiStirlingFirst n (k + 1) ζ := by
  exact jacobiStirlingFirst_recurrence n k ζ

#print axioms jacobiStirlingFirstPoly
#print axioms jacobiStirlingFirst
#print axioms jacobiStirlingFirst_initial_row
#print axioms jacobiStirlingFirst_recurrence
#print axioms jacobiStirlingFirst_support
#print axioms jacobiStirlingFirst_diagonal

end MetaMathlibExt
