import Mathlib.Basic.Real.Basic

namespace ProbabilityTheory

/-- Pointwise sum of a real and a real random variable: c + f is un ω => c + f ω,
lifting c to the constant RV un _ => c. Available under open scoped ProbabilityTheory.
Does not add a Coe ℝ (Ω → ℝ). -/
scoped instance instHAddRealFun {Ω : Type*} : HAdd ℝ (Ω → ℝ) (Ω → ℝ) where
  hAdd c f := (fun _ => c) + f

/-- Pointwise sum of a real random variable and a real:  + c is un ω => f ω + c,
lifting c to the constant RV un _ => c. Available under open scoped ProbabilityTheory.
Does not add a Coe ℝ (Ω → ℝ). -/
scoped instance instHAddFunReal {Ω : Type*} : HAdd (Ω → ℝ) ℝ (Ω → ℝ) where
  hAdd f c := f + (fun _ => c)

variable {Ω : Type*}

@[simp] theorem real_add_fun_apply (c : ℝ) (f : Ω → ℝ) (ω : Ω) :
    (c + f) ω = c + f ω :=
  rfl

@[simp] theorem fun_add_real_apply (f : Ω → ℝ) (c : ℝ) (ω : Ω) :
    (f + c) ω = f ω + c :=
  rfl

end ProbabilityTheory
