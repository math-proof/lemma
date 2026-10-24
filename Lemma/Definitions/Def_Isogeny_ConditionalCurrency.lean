import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_WeierstrassCurve_GenusOnePic0

set_option autoImplicit false

noncomputable section IsogenyCurrency

section Delta

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace Pic0

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
variable (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)

def pushforwardAlongDegZero :
    Divisor.degZero (K := K) (F := F') →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pushforwardAlong φ hφ).domRestrict
    (Divisor.degZero (K := K) (F := F'))).codRestrict _
    (fun D => Divisor.pushforwardAlong_mem_degZero φ hφ D.2)

@[simp]
theorem coe_pushforwardAlongDegZero (D : Divisor.degZero (K := K) (F := F')) :
    (pushforwardAlongDegZero φ hφ D : Divisor K F) =
      Divisor.pushforwardAlong φ hφ (D : Divisor K F') :=
  rfl

def pushforwardAlongHom : Pic0 K F' →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (pushforwardAlongDegZero φ hφ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong φ hφ hfin hN hD)

theorem pushforwardAlongHom_mk (D : Divisor.degZero (K := K) (F := F')) :
    pushforwardAlongHom φ hφ hfin hN (mk D) = mk (pushforwardAlongDegZero φ hφ D) :=
  rfl

end Pic0

end AlgebraicCurve

end Delta

open AlgebraicCurve

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem Place.deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

end AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]
variable [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

theorem inertiaDegAlong_eq_one (w : AlgebraicCurve.Place F W.FunctionField) :
    w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rw [deg_eq_one (W := V) (w.restrictAlong ι hι), deg_eq_one (W := W) w, one_mul] at h
  exact h

theorem pushforwardAlong_single_eq (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    Divisor.pushforwardAlong ι hι (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one ι hι w, Nat.cast_one, mul_one]

variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)

theorem pushforwardAlongDegZero_pointDivisor {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongDegZero ι hι (pointDivisor P) = pointDivisor Q := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq ι hι, pushforwardAlong_single_eq ι hι, hP, h0]

theorem pushforwardAlongHom_pointClass {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P) = pointClass Q := by
  show Pic0.pushforwardAlongHom ι hι hfin hN (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor Q)
  rw [Pic0.pushforwardAlongHom_mk, pushforwardAlongDegZero_pointDivisor ι hι hP h0]

def pointMapOfPushforward : W.Point →+ V.Point :=
  ((genusOnePic0Equiv V).toAddMonoidHom.comp
      (Pic0.pushforwardAlongHom ι hι hfin hN)).comp
    (genusOnePic0Equiv W).symm.toAddMonoidHom

@[simp]
theorem pointMapOfPushforward_apply (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = genusOnePic0Equiv V (Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P)) := by
  rw [← genusOnePic0Equiv_symm_apply]
  rfl

theorem pointMapOfPushforward_eq_of_seam (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P)) (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P = g P := by
  rw [pointMapOfPushforward_apply,
    pushforwardAlongHom_pointClass ι hι hfin hN (hg P) ((hg 0).trans (by rw [hg0])),
    genusOnePic0Equiv_apply, pic0ToPoint_pointClass]

include hfin hN in

theorem map_add_of_seam (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P)) (P Q : W.Point) :
    g (P + Q) = g P + g Q := by
  rw [← pointMapOfPushforward_eq_of_seam ι hι hfin hN g hg0 hg (P + Q),
    ← pointMapOfPushforward_eq_of_seam ι hι hfin hN g hg0 hg P,
    ← pointMapOfPushforward_eq_of_seam ι hι hfin hN g hg0 hg Q, map_add]

theorem eq_zero_iff_of_seam (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P)) (P : W.Point) :
    g P = 0 ↔ Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P) = 0 := by
  rw [← pointMapOfPushforward_eq_of_seam ι hι hfin hN g hg0 hg P, pointMapOfPushforward_apply]
  constructor
  · intro h
    exact (genusOnePic0Equiv V).injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]

structure IsogenyEndDatum where

  ι : W.FunctionField →ₐ[F] W.FunctionField

  hι : ι.toRingHom.IsIntegral

  hfin : FiniteAlong F ι

namespace IsogenyEndDatum

variable {W}

def pointEnd (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) :
    AddMonoid.End W.Point :=
  pointMapOfPushforward D.ι D.hι D.hfin hN

theorem pointEnd_apply (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin)
    (P : W.Point) :
    D.pointEnd hN P
      = genusOnePic0Equiv W
          (Pic0.pushforwardAlongHom D.ι D.hι D.hfin hN (pointClass P)) :=
  pointMapOfPushforward_apply D.ι D.hι D.hfin hN P

theorem pointEnd_eq_of_seam (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin)
    (g : W.Point → W.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint (g P)) (P : W.Point) :
    D.pointEnd hN P = g P :=
  pointMapOfPushforward_eq_of_seam D.ι D.hι D.hfin hN g hg0 hg P

end IsogenyEndDatum

def isogenyEndSubring (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin) :
    Subring (AddMonoid.End W.Point) :=
  Subring.closure (Set.range (fun D => IsogenyEndDatum.pointEnd D (hNs D)))

theorem IsogenyEndDatum.pointEnd_mem_isogenyEndSubring
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin) (D : IsogenyEndDatum W) :
    D.pointEnd (hNs D) ∈ isogenyEndSubring W hNs :=
  Subring.subset_closure ⟨D, rfl⟩

structure IsogenyHomDatum (V₀ V₁ : Affine F) where
  ι : V₁.FunctionField →ₐ[F] V₀.FunctionField
  hι : ι.toRingHom.IsIntegral
  hfin : FiniteAlong F ι

namespace IsogenyHomDatum

variable {V₀ V₁ : Affine F} [V₀.IsElliptic] [V₁.IsElliptic]
variable [GenusOnePlaceGate V₀] [AbelTheorem V₀] [GenusOnePlaceGate V₁] [AbelTheorem V₁]

def pointHom (D : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F D.ι D.hfin) :
    V₀.Point →+ V₁.Point :=
  pointMapOfPushforward D.ι D.hι D.hfin hN

theorem pointHom_apply (D : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F D.ι D.hfin)
    (P : V₀.Point) :
    D.pointHom hN P = genusOnePic0Equiv V₁
      (Pic0.pushforwardAlongHom D.ι D.hι D.hfin hN (pointClass P)) :=
  pointMapOfPushforward_apply D.ι D.hι D.hfin hN P

theorem pointHom_eq_of_seam (D : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F D.ι D.hfin)
    (g : V₀.Point → V₁.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint (g P))
    (P : V₀.Point) :
    D.pointHom hN P = g P :=
  pointMapOfPushforward_eq_of_seam D.ι D.hι D.hfin hN g hg0 hg P

def ofEndDatum {W' : Affine F} (D : IsogenyEndDatum W') : IsogenyHomDatum W' W' where
  ι := D.ι
  hι := D.hι
  hfin := D.hfin

end IsogenyHomDatum

end WeierstrassCurve.Affine

end IsogenyCurrency
