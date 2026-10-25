/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/ResidueClassPsi.lean -/


import Mathlib.NumberTheory.Chebyshev
import Def.NumberTheory.PrimeCounting.ResidueClassPsi
import Lemma.Nat.PrimeCounting.ResidueClassPsi


example {q : ℕ} (a : ZMod q) : Chebyshev.psiResidueClass a 0 = 0 := by
  exact Chebyshev.psiResidueClass_of_lt_one a zero_lt_one

example {q : ℕ} (a : ZMod q) : Chebyshev.psiResidueClass a (-3) = 0 := by
  exact Chebyshev.psiResidueClass_of_lt_one a (by norm_num)

example (x : ℝ) : Chebyshev.psiResidueClass (0 : ZMod 1) x = Chebyshev.psi x := by
  unfold Chebyshev.psiResidueClass Chebyshev.psi
    ArithmeticFunction.vonMangoldt.residueClass
  apply Finset.sum_congr rfl
  intro n _
  rw [Set.indicator_of_mem]
  exact Subsingleton.elim _ _

