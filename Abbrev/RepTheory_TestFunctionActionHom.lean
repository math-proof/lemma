module

public import Abbrev.RepTheory_TestFunctionAction
public import Abbrev.LanglandsTunnell_SchwartzBruhatSpace
public import Def.RepTheory_SmoothAdmissibleSchurCommutant
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace LevelMeasure

section Mass

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

end Mass

section Indicator

variable {G : Type} [Group G]

end Indicator

end LevelMeasure

namespace ModuleAction

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev ofHom (π : G →* Module.End ℂ V) : DistribMulAction G V :=
  DistribMulAction.compHom V π

end ModuleAction

open MeasureTheory
open scoped Topology

namespace TestFunctionAction

section Smooth

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G] [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : G →* Module.End ℂ V)

end Smooth

section Bundle

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
  [OpensMeasurableSpace G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

end Bundle

end TestFunctionAction
