module

public import Theorem.Hyperreal.UFn.of.All_UFn
public import Theorem.Int.Abs.eq.Max_Neg
public import Theorem.Analysis.SpecialFunctions.Exponential

@[expose] public section

open Filter Hyperreal Int


/-- the exponential function as a monoid hom from `Multiplicative ℝ*` to `ℝ*` -/
@[simps]
noncomputable def Hyperreal.expMonoidHom : MonoidHom (Multiplicative ℝ*) ℝ* :=
  {
    toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add]
  }

