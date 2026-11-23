import Mathlib
import Def.ModularCurve_KatzLevelP
import Def.ModularCurve_KatzLevelPUniversal
import Def.ModularCurve_KatzLevelPClassifyingMaps
import Instance.ModularCurve_KatzLevelPTorusPairs

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section Torus

variable (p : ℕ) (a b : ℕ)

def torusX : UnivBasisRing p :=
  ((univCurveT p).Φ a).eval (univData p).xP * Ring.inverse (((univCurveT p).ΨSq a).eval (univData p).xP)

def torusQuadratic : Polynomial (UnivBasisRing p) :=
  X ^ 2 + C ((univCurveT p).a₁ * torusX p a + (univCurveT p).a₃) * X -
    C (torusX p a ^ 3 + (univCurveT p).a₂ * torusX p a ^ 2 + (univCurveT p).a₄ * torusX p a +
      (univCurveT p).a₆)

abbrev TorusQRing : Type :=
  AdjoinRoot ((torusQuadratic p a).map (algebraMap (UnivBasisRing p) (BorelQRing p b)))

def TorusQRing.ofUniv : UnivBasisRing p →+* TorusQRing p a b :=
  (AdjoinRoot.of _).comp (algebraMap (UnivBasisRing p) (BorelQRing p b))

def TorusQRing.xP : TorusQRing p a b := TorusQRing.ofUniv p a b (torusX p a)

def TorusQRing.yP : TorusQRing p a b := AdjoinRoot.root _

def TorusQRing.xQ : TorusQRing p a b := TorusQRing.ofUniv p a b (borelX p b)

def TorusQRing.yQ : TorusQRing p a b := AdjoinRoot.of _ (borelQY p b)

def torusQCurve : WeierstrassCurve (TorusQRing p a b) := (univCurveT p).map (TorusQRing.ofUniv p a b)

def torusQData' : LevelPData (TorusQRing p a b) :=
  ⟨TorusQRing.xP p a b, TorusQRing.yP p a b, TorusQRing.xQ p a b, TorusQRing.yQ p a b⟩

def torusDenom : TorusQRing p a b :=
  indepElt (torusQCurve p a b) p (TorusQRing.xP p a b) (TorusQRing.xQ p a b) *
    indepElt (torusQCurve p a b) p (TorusQRing.xQ p a b) (TorusQRing.xP p a b)

def TorusRing : Type := Localization.Away (torusDenom p a b)

def TorusRing.ofUniv : UnivBasisRing p →+* TorusRing p a b := algebraMap (UnivBasisRing p) (TorusRing p a b)

def torusCurve : WeierstrassCurve (TorusRing p a b) := (univCurveT p).map (TorusRing.ofUniv p a b)

def torusData : LevelPData (TorusRing p a b) := (univData p).map (TorusRing.ofUniv p a b)

def torusData' : LevelPData (TorusRing p a b) :=
  (torusQData' p a b).map (algebraMap (TorusQRing p a b) (TorusRing p a b))

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
  (hD' : IsLevelPStructure ((univCurveT p).map φ) p D')
  (hxP : D'.xP = φ (torusX p a)) (hxQ : D'.xQ = φ (borelX p b))

include hD' hxP in
def TorusQRing.lift : TorusQRing p a b →+* T :=
  AdjoinRoot.lift (BorelQRing.lift p b φ D' hD' hxQ) D'.yP (by
    rw [Polynomial.eval₂_map]
    have h : (BorelQRing.lift p b φ D' hD' hxQ).comp (algebraMap (UnivBasisRing p) (BorelQRing p b)) = φ := by
      rw [AdjoinRoot.algebraMap_eq]
      exact RingHom.ext (BorelQRing.lift_of p b φ D' hD' hxQ)
    rw [h]
    exact torusQuadratic_eval₂_eq_zero p a φ D' hD' hxP)

def TorusRing.lift : TorusRing p a b →+* T :=
  IsLocalization.Away.lift (torusDenom p a b) (g := TorusQRing.lift p a b φ D' hD' hxP hxQ)
    (by rw [TorusQRing.lift_torusDenom]; exact hD'.isUnit_indepElt_PQ.mul hD'.isUnit_indepElt_QP)

end Torus

end LevelP

end ModularCurve

end
