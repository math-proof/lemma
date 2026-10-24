import Lemma.Definitions.Def_ModularCurve_AtkinLehner
import Lemma.Definitions.Def_ModularCurve_GeometricBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (N : ℕ) [NeZero N]

def frickeInvolutionBar :
    modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
  geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)

theorem frickeInvolutionBar_def :
    frickeInvolutionBar N =
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N) :=
  rfl

def cuspZeroBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  frickeInvolutionBar N • cuspInftyBar N

theorem cuspZeroBar_def : cuspZeroBar N = frickeInvolutionBar N • cuspInftyBar N := rfl

def cuspidalDivisor : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1

theorem cuspidalDivisor_def :
    cuspidalDivisor N = Finsupp.single (cuspZeroBar N) 1 - Finsupp.single (cuspInftyBar N) 1 :=
  rfl

theorem degree_cuspidalDivisor : Divisor.degree (cuspidalDivisor N) = 0 := by
  rw [cuspidalDivisor_def, map_sub, Divisor.degree_single, Divisor.degree_single, cuspZeroBar_def,
    Place.deg_smul, sub_self]

def cuspidalDivisor₀ :
    Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
  ⟨cuspidalDivisor N, Divisor.mem_degZero.mpr (degree_cuspidalDivisor N)⟩

@[simp]
theorem coe_cuspidalDivisor₀ :
    (cuspidalDivisor₀ N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) =
      cuspidalDivisor N :=
  rfl

def cuspidalClass : JZero N := Pic0.mk (cuspidalDivisor₀ N)

theorem cuspidalClass_def : cuspidalClass N = Pic0.mk (cuspidalDivisor₀ N) := rfl

end ModularCurve

end
