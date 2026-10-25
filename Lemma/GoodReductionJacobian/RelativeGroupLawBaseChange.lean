import Mathlib.AlgebraicGeometry.Pullbacks
import Lemma.GoodReductionJacobian.RelativeGroupLawKernel
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension
import Lemma.AlgebraicGeometry.NeronSpecialFibreRestriction
import Lemma.GoodReductionJacobian.RelativeGroupLawFibre
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section BaseChange

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}


def baseChangePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) : SchemeHomOver (t' ≫ ι) f :=
  ⟨x.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def baseChangePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) : SchemeHomOver t' (baseChangeStr ι f) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem baseChangePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (baseChangePointToBase ι x).1 = x.1 ≫ pullback.fst f ι :=
  rfl

@[simp]
theorem baseChangePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    (baseChangePointOfBase ι y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem baseChangePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    baseChangePointToBase ι (baseChangePointOfBase ι y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem baseChangePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointOfBase ι (baseChangePointToBase ι x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [baseChangePointOfBase_coe, pullback.lift_fst, baseChangePointToBase_coe]
  · rw [baseChangePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def baseChangePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    SchemeHomOver t' (baseChangeStr ι f) ≃ SchemeHomOver (t' ≫ ι) f where
  toFun := baseChangePointToBase ι
  invFun := baseChangePointOfBase ι
  left_inv := baseChangePointOfBase_toBase ι
  right_inv := baseChangePointToBase_ofBase ι

theorem baseChangePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) (t' : T' ⟶ Spec (CommRingCat.of R')) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t (baseChangeStr ι f)) :
    baseChangePointToBase ι (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem baseChangePointToBase_comp_fibreRestrictAlong {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t' (baseChangeStr ι g)) :
    baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase ι x) φ := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    fibreRestrictAlong_coe_comp_fst]

def baseChange (G : RelativeGroupLaw R f) : RelativeGroupLaw R' (baseChangeStr ι f) where
  mul t' x y := baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y))
  one t' := baseChangePointOfBase ι (G.one _)
  inv t' x := baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x))
  mul_assoc t' x y z := by
    simp only [baseChangePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [baseChangePointToBase_ofBase, G.one_mul, baseChangePointOfBase_toBase]
  mul_one t' x := by
    simp only [baseChangePointToBase_ofBase, G.mul_one, baseChangePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [baseChangePointToBase_ofBase, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_fst, pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ ι) (t' ≫ ι) ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x)
          (baseChangePointToBase ι y))
      rw [schemeHomOverComp_coe] at h
      rw [h, ← baseChangePointToBase_schemeHomOverComp, ← baseChangePointToBase_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe, Category.assoc,
        pullback.lift_snd, pullback.lift_snd]
      exact hψ

@[simp]
theorem baseChange_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).mul t' x y =
      baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y)) :=
  rfl

@[simp]
theorem baseChange_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (G.baseChange ι).one t' = baseChangePointOfBase ι (G.one _) :=
  rfl

@[simp]
theorem baseChange_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).inv t' x = baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x)) :=
  rfl

theorem baseChangePointToBase_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).mul t' x y) =
      G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y) := by
  rw [baseChange_mul, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) :
    baseChangePointToBase ι ((G.baseChange ι).one t') = G.one _ := by
  rw [baseChange_one, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).inv t' x) = G.inv _ (baseChangePointToBase ι x) := by
  rw [baseChange_inv, baseChangePointToBase_ofBase]

theorem IsCommutative.baseChange {G : RelativeGroupLaw R f} (hG : G.IsCommutative) :
    (G.baseChange ι).IsCommutative := fun t' x y => by
  rw [baseChange_mul, baseChange_mul, hG.mul_comm]

theorem fibre_eq_baseChange (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    G.fibre s = G.baseChange (basePointInclusion s) :=
  rfl

end BaseChange

section GenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}


abbrev genericFibre (G : RelativeGroupLaw R f) : RelativeGroupLaw K (genericFibreStr K f) :=
  G.baseChange (specGenericFibreInclusion R K)

theorem baseChangePointToBase_comp_genericFibreRestrict {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t' (genericFibreStr K g)) :
    baseChangePointToBase (specGenericFibreInclusion R K)
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase (specGenericFibreInclusion R K) x) φ :=
  baseChangePointToBase_comp_fibreRestrictAlong (specGenericFibreInclusion R K) φ x

end GenericFibre

end RelativeGroupLaw
end GoodReductionJacobian

end
