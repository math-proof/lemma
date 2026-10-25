import Structure.CerednikDrinfeld_Ribbon
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Instance.CerednikDrinfeld_MumfordPeriod
import Class.CerednikDrinfeld_MumfordPeriod
import Structure.CerednikDrinfeld_MumfordPeriod

set_option autoImplicit false
noncomputable section
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
