import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Class.Analysis.SpecialFunctions.Exponential.Part4
open Filter Hyperreal Int


noncomputable instance : Log ℝ where
  log := Real.log
  log_zero := Real.log_zero
  log_one := Real.log_one
  log_div_self := Real.log_div_self

noncomputable instance : Log ℂ where
  log := Complex.log
  log_zero := Complex.log_zero
  log_one := Complex.log_one
  log_div_self := Complex.log_div_self

noncomputable instance : Log ℝ* where
  log x := x.map Real.log
  log_zero := by
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_zero]
  log_one := by
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_one]
  log_div_self x := by
    apply UFn.of.All_UFn x
    intro x
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_div_self]


