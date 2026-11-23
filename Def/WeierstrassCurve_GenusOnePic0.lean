module

public import Mathlib
public import Class.AlgebraicCurve_DivisorClassGroup
public import Class.WeierstrassCurve_GenusOnePic0
public import Abbrev.WeierstrassCurve_GenusOnePic0

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

variable {W : Affine F} [GenusOnePlaceGate W]

def placeOfPoint : W.Point → AlgebraicCurve.Place F W.FunctionField :=
  pointEquivPlace (W := W)

def pointDivisor (P : W.Point) : Divisor.degZero (K := F) (F := W.FunctionField) :=
  ⟨Finsupp.single (placeOfPoint P) 1 - Finsupp.single (placeOfPoint (0 : W.Point)) 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      deg_placeOfPoint, deg_placeOfPoint, sub_self]⟩

def pointClass (P : W.Point) : AlgebraicCurve.Pic0 F W.FunctionField :=
  Pic0.mk (pointDivisor P)

section AbelTheorem

variable [AbelTheorem W]

def pic0ToPoint : AlgebraicCurve.Pic0 F W.FunctionField →+ W.Point :=
  QuotientAddGroup.lift _
    (divisorSum.comp (Divisor.degZero (K := F) (F := W.FunctionField)).subtype)
    (by
      rintro ⟨D, hD0⟩ hD
      rw [AddSubgroup.mem_addSubgroupOf] at hD
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype]
      exact divisorSum_eq_zero_of_isPrincipal (Divisor.mem_degZero.mp hD0)
        (Divisor.mem_principal.mp hD))

variable (W) in

def genusOnePic0Equiv : AlgebraicCurve.Pic0 F W.FunctionField ≃+ W.Point :=
  AddEquiv.ofBijective pic0ToPoint ⟨pic0ToPoint_injective, pic0ToPoint_surjective⟩

end AbelTheorem

end WeierstrassCurve.Affine

end

end
