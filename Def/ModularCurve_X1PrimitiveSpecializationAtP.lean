module
public import Mathlib
public import Def.FLTPrelim_Ramification
public import Instance.EllipticCurve_FrobeniusTrace
public import Instance.EllipticCurve_TateModule
public import Theorem.MvPolynomial.X1HeckeModule
public import Def.ModularCurve_X1PrimitiveSpecialization
public import Theorem.LaurentSeries.QExpFrobeniusModL
set_option autoImplicit false


public section

noncomputable section

open IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

variable (M p : ℕ)

def normFreeRepsAt : Finset ℕ :=
  (Finset.range M).filter (fun d => Nat.Coprime d M ∧ d ≡ 1 [MOD M / p])


def normFreePartAt : AddSubgroup (JOne M) :=
  (normFreeEnd M (normFreeRepsAt M p)).range

end NormFree

end ModularCurve

end
