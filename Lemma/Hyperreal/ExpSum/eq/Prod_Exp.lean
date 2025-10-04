import sympy.functions.elementary.exponential
import sympy.Basic

/--
[DecidableEq ι] is not required in Real.exp_sum
-/
@[main]
private lemma main
-- given
  (s : Finset ι)
  (f : ι → ℝ*) :
-- imply
  exp (∑ x ∈ s, f x) = ∏ x ∈ s, exp (f x) :=
-- proof
  map_prod (M := Multiplicative ℝ*) Hyperreal.expMonoidHom f s
  -- induction s using Finset.induction_on with
  -- | empty =>
  --   simp [Exp.exp_zero]
  -- | insert j s hj ih =>
  --   simp_all
  --   rw [Exp.exp_add]
  --   rw [ih]


-- created on 2025-10-04
