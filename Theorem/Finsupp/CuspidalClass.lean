module

public import Theorem.HahnSeries.AtkinLehner
public import Theorem.LaurentSeries.GeometricBaseChange

public noncomputable section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (N : ℕ) [NeZero N]


public theorem frickeInvolutionBar_def :
    frickeInvolutionBar N =
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N) :=
  rfl


public theorem cuspZeroBar_def : cuspZeroBar N = frickeInvolutionBar N • cuspInftyBar N := rfl


public theorem cuspidalDivisor_def :
    cuspidalDivisor N = Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1 :=
  rfl


public theorem degree_cuspidalDivisor : Divisor.degree (cuspidalDivisor N) = 0 := by
  rw [cuspidalDivisor_def, map_sub, Divisor.degree_single, Divisor.degree_single, cuspZeroBar_def,
    Place.deg_smul, sub_self]


@[simp]
public theorem coe_cuspidalDivisor₀ :
    (cuspidalDivisor₀ N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) =
      cuspidalDivisor N :=
  rfl


public theorem cuspidalClass_def : cuspidalClass N = Pic0.mk (cuspidalDivisor₀ N) := rfl

end ModularCurve

end
