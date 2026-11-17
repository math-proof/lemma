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

set_option autoImplicit false
public noncomputable section
namespace CerednikDrinfeld
namespace Mumford

open ModularCurve MulAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]


variable (G) in


variable (G) in


variable (G) in


variable (G) in


structure PeriodDatum {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (K L : Type) [Field K] [Field L] [Algebra K L] (ord : Additive Kˣ →+ ℤ) where

  Q : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D) →ₗ[ℤ] Additive Kˣ

  Q_symm : ∀ x y, Q x y = Q y x

  ord_Q : ∀ x y, ord (Q x y) = ribbonGram D x y


namespace PeriodDatum
variable {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)

set_option linter.unusedVariables false in


end PeriodDatum

end Mumford
end CerednikDrinfeld
end
