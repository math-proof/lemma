import Mathlib
import Structure.ModularCurve_JZeroNeronIdentityComponent
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
import Lemma.ModularCurve.ReductionOfPointsAgreesModL
import Lemma.ModularCurve.JZeroSemistableSpecialization
import Def.ModularCurve_JZeroNeronData
import Lemma.ModularCurve.ToricDescentData
import Def.GaloisRep_Flat
import Def.FLTPrelim_Ramification
import Lemma.ModularCurve.SupersingularNodePlaces
import Structure.JacJ1Iface
import Structure.ModularCurve_JZeroNeronObjectAtP
import Abbrev.ModularCurve_JZeroNeronObjectAtP

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

namespace JZeroNeronObjectAtP


def overId {B T X : Scheme.{0}} {ι : T ⟶ B} {f : X ⟶ B} (x : SchemeHomOver ι f) :
    SchemeHomOver (𝟙 T ≫ ι) f :=
  ⟨x.1, by rw [Category.id_comp]; exact x.2⟩

def toFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver ι f) : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f) :=
  RelativeGroupLaw.baseChangePointOfBase ι (overId x)

def ofFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : SchemeHomOver ι f :=
  ⟨(RelativeGroupLaw.baseChangePointToBase ι y).1, by
    simpa only [Category.id_comp] using (RelativeGroupLaw.baseChangePointToBase ι y).2⟩

def fibreMap {R R' : Type} [CommRing R] [CommRing R'] {X Y : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι f))
    (x : SchemeHomOver ι g) : SchemeHomOver ι f :=
  ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt x) φ)


def castOverEquiv {B T X : Scheme.{0}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') :
    SchemeHomOver ι f ≃ SchemeHomOver ι' f where
  toFun := castOver h
  invFun := castOver h.symm
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl


namespace LevelData

variable {N₀ p : ℕ} [NeZero N₀] {A : ValuationSubring (AlgebraicClosure ℚ)}

def ptsA (Λ : LevelData N₀ p A) : JZero N₀ ≃ SchemeHomOver (barPt A ≫ Λ.σA) Λ.f :=
  Λ.pts.trans (castOverEquiv Λ.hσA.symm)

def IsJacobian (Λ : LevelData N₀ p A) : Prop :=
  letI := heckeModuleBar N₀
  AbelianSchemePropertyBundle (baseRing p) Λ.f ∧
  (∀ {T : Scheme.{0}} (t : T ⟶ base p) (x y : SchemeHomOver t Λ.f), Λ.L.mul t x y = Λ.L.mul t y x) ∧
  (∀ x y : JZero N₀, Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y)) ∧
  (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero N₀),
    (Λ.pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (Λ.pts x).1) ∧
  (∀ u v : JZeroC (ResidueField ↥A) N₀, Λ.ptsSp (u + v) = Λ.L.mul _ (Λ.ptsSp u) (Λ.ptsSp v)) ∧
  (ReductionInputsModL A N₀ → ReductionOfPointsAgreesModL N₀ A Λ.f Λ.σA Λ.ptsA Λ.ptsSp) ∧
  (∀ t : HeckeAlg, ∃ φ : SchemeHomOver Λ.f Λ.f,
    (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      NeronModelInfra.schemeHomOverComp (Λ.L.mul s x y) φ =
        Λ.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
    ∀ x : JZero N₀, (Λ.pts (t • x)).1 = (Λ.pts x).1 ≫ φ.1)

end LevelData

end JZeroNeronObjectAtP

open JZeroNeronObjectAtP

attribute [local instance] instDecidableEqResidueFieldSemistable
  instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in


namespace JZeroNeronObjectAtP

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

def toricPoint (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) : JZero (N₀ * p) :=
  O.pts.symm (genOfBaseChangePt Λ.hσA
    (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (O.toricLift m hm)))

def toricPts (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) : AddSubgroup (JZero (N₀ * p)) :=
  if hm : 0 < m then AddSubgroup.closure (Set.range (O.toricPoint m hm)) else ⊥

def finPts (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) : AddSubgroup (JZero (N₀ * p)) :=
  AddSubgroup.closure {x | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x)}

end JZeroNeronObjectAtP

end ModularCurve

end
