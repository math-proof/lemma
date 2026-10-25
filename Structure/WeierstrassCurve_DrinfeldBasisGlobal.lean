import Mathlib
import Structure.WeierstrassCurve_ProjModel
import Abbrev.AlgebraicGeometry_RelEffCartierDivSum
import Structure.ModularCurve_WeierstrassLevelComponents

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev base : Scheme.{u} := Spec (CommRingCat.of T)

abbrev Section : Type u := SchemeHomOver (𝟙 (base (T := T))) (projModelStrCR W)

variable {W}

def linComb (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) (a b : ℕ) : Section W :=
  G.mul _ (G.nsmul _ a P) (G.nsmul _ b Q)

def basisTuple (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) :
    Fin (q * q) → (base (T := T) ⟶ projModelCR W) :=
  fun i => (linComb G P Q (i.val / q) (i.val % q)).1

theorem basisTuple_over (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) (i : Fin (q * q)) :
    basisTuple G q P Q i ≫ projModelStrCR W = 𝟙 _ :=
  (linComb G P Q (i.val / q) (i.val % q)).2

def basisDivisor (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) :
    (pullback (projModelStrCR W) (𝟙 (base (T := T)))).IdealSheafData :=
  prodKerGraph (projModelStrCR W) (basisTuple G q P Q) (basisTuple_over G q P Q)

def toPullbackId : projModelCR W ⟶ pullback (projModelStrCR W) (𝟙 (base (T := T))) :=
  pullback.lift (𝟙 _) (projModelStrCR W) (by simp)

def torsionIdeal (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) :
    (pullback (projModelStrCR W) (𝟙 (base (T := T)))).IdealSheafData :=
  (pullback.fst (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ toPullbackId).ker

def IsDrinfeldBasis (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W) : Prop :=
  basisDivisor G q P Q = torsionIdeal G q

abbrev GroupLawFamily (A : Type u) [CommRing A] : Type (u + 1) :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T), RelativeGroupLaw T (projModelStrCR W)


structure RawDrinfeldPair (T : Type u) [CommRing T] where

  curve : WeierstrassCurve.Projective T

  P : Section curve

  Q : Section curve

def IsDrinfeldLevel {A : Type u} [CommRing A] (𝒢 : GroupLawFamily A) (q : ℕ)
    {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) : Prop :=
  x.curve = W ∧ IsDrinfeldBasis (𝒢 T x.curve) q x.P x.Q

structure DrinfeldTransport (A : Type u) [CommRing A] (𝒢 : GroupLawFamily A) (q : ℕ) where

  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → RawDrinfeldPair T → RawDrinfeldPair T'

  act : {T : Type u} → [CommRing T] → [Algebra A T] →
    WeierstrassCurve.VariableChange T → RawDrinfeldPair T → RawDrinfeldPair T
  map_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : RawDrinfeldPair T), map (AlgHom.id A T) x = x
  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : RawDrinfeldPair T),
    map (g.comp f) x = map g (map f x)
  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : RawDrinfeldPair T),
    act (1 : WeierstrassCurve.VariableChange T) x = x
  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T)
    (x : RawDrinfeldPair T), act (C * C') x = act C (act C' x)
  map_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T),
    map f (act C x) = act (C.map f.toRingHom) (map f x)
  isLevel_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T),
    IsDrinfeldLevel 𝒢 q W x → IsDrinfeldLevel 𝒢 q (W.map f.toRingHom) (map f x)
  isLevel_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T),
    IsDrinfeldLevel 𝒢 q W x → IsDrinfeldLevel 𝒢 q (C • W) (act C x)


end WeierstrassCurve.DrinfeldGlobal

end
