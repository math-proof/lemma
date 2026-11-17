module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MulConvolution

open MeasureTheory Set Filter Topology

variable {G : Type*} [Group G] [MeasurableSpace G]

def mulConv (μ : Measure G) (f g : G → ℂ) : G → ℂ := fun x => ∫ y, f y * g (y⁻¹ * x) ∂μ

end MulConvolution

end
