import Mathlib
import Lemma.ModularCurve.IgusaFunctionField
import Lemma.ModularCurve.X1
import Structure.ModularCurve_IgusaFunctionFieldX1

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve

variable (κ : Type*) [Field κ] (M : ℕ)


variable {κ M}

def IntegralWeightOneForm.hasseRootFn (w : IntegralWeightOneForm κ M) : LaurentSeries κ :=
  (intSeriesC κ w.series)⁻¹

theorem IntegralWeightOneForm.hasseRootFn_ne_zero (w : IntegralWeightOneForm κ M) : w.hasseRootFn ≠ 0 :=
  inv_ne_zero w.intSeriesC_ne_zero

variable (κ M)

def igusaFunctionFieldX1C (w : IntegralWeightOneForm κ M) : IntermediateField κ (LaurentSeries κ) :=
  IgusaCover.igusaFunctionField (x1FunctionFieldC κ M) w.hasseRootFn

theorem x1FunctionFieldC_le_igusaFunctionFieldX1C (w : IntegralWeightOneForm κ M) :
    x1FunctionFieldC κ M ≤ igusaFunctionFieldX1C κ M w :=
  IgusaCover.le_igusaFunctionField _ _

theorem hasseRootFn_mem_igusaFunctionFieldX1C (w : IntegralWeightOneForm κ M) :
    w.hasseRootFn ∈ igusaFunctionFieldX1C κ M w :=
  IgusaCover.mem_igusaFunctionField _ _

abbrev IgusaDiamondDataX1C (w : IntegralWeightOneForm κ M) (p : ℕ) [Fact p.Prime] [CharP κ p] :=
  IgusaCover.IgusaDiamondData p (-1) (x1FunctionFieldC κ M) w.hasseRootFn

end ModularCurve

end
