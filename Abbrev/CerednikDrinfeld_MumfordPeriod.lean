module

public import Structure.CerednikDrinfeld_Ribbon
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Instance.CerednikDrinfeld_MumfordPeriod
public import Class.CerednikDrinfeld_MumfordPeriod
public import Structure.CerednikDrinfeld_MumfordPeriod

set_option autoImplicit false
@[expose] public noncomputable section
namespace CerednikDrinfeld
namespace Mumford

open ModularCurve MulAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

abbrev QuotEdge (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯] :=
  orbitRel.Quotient G 𝒯.Dart

abbrev QuotVert (G : Type) [Group G] (W : Type) [MulAction G W] := orbitRel.Quotient G W


namespace PeriodDatum
variable {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)

set_option linter.unusedVariables false in

abbrev TorusPoints (P : PeriodDatum D K L ord) : Type := ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ
end PeriodDatum

end Mumford
end CerednikDrinfeld
end
