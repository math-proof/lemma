import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Lemma.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev baseResidueField (s : (Spec (CommRingCat.of R) : Scheme.{u})) : Type u :=
  (Spec (CommRingCat.of R)).residueField s

abbrev basePointInclusion (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Spec (CommRingCat.of (baseResidueField s)) ⟶ Spec (CommRingCat.of R) :=
  (Spec (CommRingCat.of R)).fromSpecResidueField s

abbrev fibreScheme (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Scheme.{u} :=
  pullback f (basePointInclusion s)

abbrev fibreStr (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    fibreScheme f s ⟶ Spec (CommRingCat.of (baseResidueField s)) :=
  pullback.snd f (basePointInclusion s)

variable (s : (Spec (CommRingCat.of R) : Scheme.{u}))

theorem fibreScheme_eq_fiber : fibreScheme f s = f.fiber s := rfl

theorem fibreStr_eq_fiberToSpecResidueField :
    fibreStr f s = f.fiberToSpecResidueField s := rfl

def fibrePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) : SchemeHomOver (t' ≫ basePointInclusion s) f :=
  ⟨x.1 ≫ pullback.fst f (basePointInclusion s), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def fibrePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) : SchemeHomOver t' (fibreStr f s) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem fibrePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) :
    (fibrePointToBase s x).1 = x.1 ≫ pullback.fst f (basePointInclusion s) :=
  rfl

@[simp]
theorem fibrePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) :
    (fibrePointOfBase s y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem fibrePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) :
    fibrePointToBase s (fibrePointOfBase s y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem fibrePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) :
    fibrePointOfBase s (fibrePointToBase s x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [fibrePointOfBase_coe, pullback.lift_fst, fibrePointToBase_coe]
  · rw [fibrePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def fibrePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) :
    SchemeHomOver t' (fibreStr f s) ≃ SchemeHomOver (t' ≫ basePointInclusion s) f where
  toFun := fibrePointToBase s
  invFun := fibrePointOfBase s
  left_inv := fibrePointOfBase_toBase s
  right_inv := fibrePointToBase_ofBase s

theorem fibrePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of (baseResidueField s)))
    (t' : T' ⟶ Spec (CommRingCat.of (baseResidueField s))) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (fibreStr f s)) :
    fibrePointToBase s (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (fibrePointToBase s x) :=
  Subtype.ext (Category.assoc _ _ _)

def fibre (G : RelativeGroupLaw R f) : RelativeGroupLaw (baseResidueField s) (fibreStr f s) where
  mul t' x y := fibrePointOfBase s (G.mul _ (fibrePointToBase s x) (fibrePointToBase s y))
  one t' := fibrePointOfBase s (G.one _)
  inv t' x := fibrePointOfBase s (G.inv _ (fibrePointToBase s x))
  mul_assoc t' x y z := by
    simp only [fibrePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [fibrePointToBase_ofBase, G.one_mul, fibrePointOfBase_toBase]
  mul_one t' x := by
    simp only [fibrePointToBase_ofBase, G.mul_one, fibrePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [fibrePointToBase_ofBase, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [schemeHomOverComp_coe, fibrePointOfBase_coe, fibrePointOfBase_coe, Category.assoc, pullback.lift_fst,
        pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ basePointInclusion s) (t' ≫ basePointInclusion s) ψ
          (by rw [← Category.assoc, hψ]) (fibrePointToBase s x) (fibrePointToBase s y))
      rw [schemeHomOverComp_coe] at h
      rw [h, ← fibrePointToBase_schemeHomOverComp, ← fibrePointToBase_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, fibrePointOfBase_coe, fibrePointOfBase_coe, Category.assoc, pullback.lift_snd,
        pullback.lift_snd]
      exact hψ

@[simp]
theorem fibre_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (x y : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).mul t' x y = fibrePointOfBase s (G.mul _ (fibrePointToBase s x) (fibrePointToBase s y)) :=
  rfl

@[simp]
theorem fibre_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) :
    (G.fibre s).one t' = fibrePointOfBase s (G.one _) :=
  rfl

@[simp]
theorem fibre_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (x : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).inv t' x = fibrePointOfBase s (G.inv _ (fibrePointToBase s x)) :=
  rfl

end RelativeGroupLaw
end GoodReductionJacobian

end
