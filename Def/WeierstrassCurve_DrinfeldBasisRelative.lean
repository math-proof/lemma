import Mathlib
import Lemma.WeierstrassCurve.ProjModel
import Abbrev.AlgebraicGeometry_RelEffCartierDivSum

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace WeierstrassProjModel.RelativeGroupLaw

variable {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}

def linCombOver (G : RelativeGroupLaw R (projModelStrCR V)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (P Q : SchemeHomOver t (projModelStrCR V)) (a b : ℕ) : SchemeHomOver t (projModelStrCR V) :=
  G.mul t (G.nsmul t a P) (G.nsmul t b Q)

def basisTupleOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) :
    Fin (q * q) → (T ⟶ projModelCR V) :=
  fun i => (G.linCombOver t P Q (i.val / q) (i.val % q)).1

theorem basisTupleOver_over (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) (i : Fin (q * q)) :
    G.basisTupleOver q t P Q i ≫ projModelStrCR V = t :=
  (G.linCombOver t P Q (i.val / q) (i.val % q)).2

def basisDivisorOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) :
    (pullback (projModelStrCR V) t).IdealSheafData :=
  prodKerGraph (projModelStrCR V) (G.basisTupleOver q t P Q) (G.basisTupleOver_over q t P Q)

def torsionIdealOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : (pullback (projModelStrCR V) t).IdealSheafData :=
  (pullback.fst (G.schemeNsmul q) (G.one (𝟙 (Spec (CommRingCat.of R)))).1).ker.comap
    (pullback.fst (projModelStrCR V) t)

def IsDrinfeldBasisOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) : Prop :=
  G.basisDivisorOver q t P Q = G.torsionIdealOver q t

end WeierstrassProjModel.RelativeGroupLaw

end
