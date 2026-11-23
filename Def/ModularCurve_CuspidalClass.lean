module

public import Theorem.HahnSeries.AtkinLehner
public import Theorem.LaurentSeries.GeometricBaseChange

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (N : ℕ) [NeZero N]

def frickeInvolutionBar :
    modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
  geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)

def cuspZeroBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  frickeInvolutionBar N • cuspInftyBar N

def cuspidalDivisor : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1

def cuspidalDivisor₀ :
    Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
  ⟨cuspidalDivisor N, Divisor.mem_degZero.mpr (degree_cuspidalDivisor N)⟩

def cuspidalClass : JZero N := Pic0.mk (cuspidalDivisor₀ N)

end ModularCurve

end
