import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Class.Analysis.SpecialFunctions.Exponential.Part5
open Filter Hyperreal Int


noncomputable instance : LogPos ℝ where
  log_mul h_x h_y := Real.log_mul h_x h_y
  log_div h_x h_y := Real.log_div h_x h_y
  log_exp x := Real.log_exp x
  exp_log_eq_abs := Real.exp_log_eq_abs

noncomputable instance : LogPos ℝ* where
  log_mul {x y} := by
    refine Germ.inductionOn₂ x y fun x y h_x h_y => ?_
    apply Germ.coe_eq.mpr
    filter_upwards [Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_x), Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_y)] with _ hn gn
    exact Real.log_mul hn gn

  log_div {x y} := by
    refine Germ.inductionOn₂ x y fun x y => ?_
    intro h_x h_y
    apply Germ.coe_eq.mpr
    filter_upwards [Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_x), Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h_y)] with _ hn gn
    exact Real.log_div hn gn

  log_exp x := by
    apply UFn.of.All_UFn x
    intro x
    apply Germ.coe_eq.mpr ∘ Eventually.of_forall
    simp [Real.log_exp]

  exp_log_eq_abs {x} := by
    apply UFn.of.All_UFn x
    intro x h
    apply Germ.coe_eq.mpr
    filter_upwards [Ultrafilter.eventually_not.mpr (mt Germ.coe_eq.mpr h)] with _ hn
    simp [Real.exp_log_eq_abs hn]
    apply Abs.eq.Max_Neg


