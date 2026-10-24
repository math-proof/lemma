import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

namespace JZeroNeronObjectAtP

attribute [local instance] instDecidableEqResidueFieldSemistable
  instAlgebraResidueFieldModularFunctionFieldCSemistable

section ShBase

variable (A : ValuationSubring (AlgebraicClosure ℚ))

abbrev invField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)

abbrev shRing : ValuationSubring ↥(invField A) :=
  A.comap (algebraMap ↥(invField A) (AlgebraicClosure ℚ))

abbrev shBase : Scheme.{0} := Spec (CommRingCat.of ↥(shRing A))

def shToPlace : ↥(shRing A) →+* ↥A :=
  ((algebraMap ↥(invField A) (AlgebraicClosure ℚ)).comp (shRing A).subtype).codRestrict A.toSubring
    (fun x => x.2)

@[simp]
theorem coe_shToPlace (x : ↥(shRing A)) :
    ((shToPlace A x : ↥A) : AlgebraicClosure ℚ) = ((x : ↥(invField A)) : AlgebraicClosure ℚ) := rfl

abbrev shPt : Spec (CommRingCat.of ↥A) ⟶ shBase A := Spec.map (CommRingCat.ofHom (shToPlace A))

end ShBase

namespace LevelData

variable {N₀ p : ℕ} [NeZero N₀] {A : ValuationSubring (AlgebraicClosure ℚ)} (Λ : LevelData N₀ p A)

def baseToPlace : baseRing p →+* ↥A := (Spec.preimage Λ.σA).hom

theorem specMap_baseToPlace : Spec.map (CommRingCat.ofHom Λ.baseToPlace) = Λ.σA := by
  rw [baseToPlace, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem coe_baseToPlace (r : baseRing p) :
    ((Λ.baseToPlace r : ↥A) : AlgebraicClosure ℚ) = algebraMap (baseRing p) (AlgebraicClosure ℚ) r := by
  have h1 := Λ.hσA
  rw [← Λ.specMap_baseToPlace, barPt, genPt, ← Spec.map_comp] at h1
  have := congrArg (fun f => (f : baseRing p →+* AlgebraicClosure ℚ) r)
    (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))
  simpa using this

theorem algebraMap_baseRing_eq (r : baseRing p) :
    algebraMap (baseRing p) (AlgebraicClosure ℚ) r = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl

def baseToSh : baseRing p →+* ↥(shRing A) where
  toFun r := ⟨⟨algebraMap (baseRing p) (AlgebraicClosure ℚ) r, by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ _
      rw [algebraMap_baseRing_eq, AlgEquiv.commutes]⟩, by
      change algebraMap (baseRing p) (AlgebraicClosure ℚ) r ∈ A
      rw [← Λ.coe_baseToPlace]; exact (Λ.baseToPlace r).2⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; apply Subtype.ext; exact map_mul _ x y
  map_zero' := by apply Subtype.ext; apply Subtype.ext; exact map_zero _
  map_add' x y := by apply Subtype.ext; apply Subtype.ext; exact map_add _ x y

theorem shToPlace_comp_baseToSh : (shToPlace A).comp Λ.baseToSh = Λ.baseToPlace := by
  ext r
  exact (Λ.coe_baseToPlace r).symm

abbrev shStr : shBase A ⟶ base p := Spec.map (CommRingCat.ofHom Λ.baseToSh)

theorem shPt_comp_shStr : shPt A ≫ Λ.shStr = Λ.σA := by
  rw [shPt, shStr, ← Spec.map_comp, ← CommRingCat.ofHom_comp, shToPlace_comp_baseToSh, specMap_baseToPlace]

theorem barPt_shPt_shStr : (barPt A ≫ shPt A) ≫ Λ.shStr = genPt p := by
  rw [Category.assoc, shPt_comp_shStr, Λ.hσA]

def shLift {X : Scheme.{0}} {f : X ⟶ base p} (s : SchemeHomOver Λ.σA f) :
    SchemeHomOver (shPt A) (RelativeGroupLaw.baseChangeStr Λ.shStr f) :=
  RelativeGroupLaw.baseChangePointOfBase Λ.shStr (castOver Λ.shPt_comp_shStr.symm s)

def shGenLift {X : Scheme.{0}} {f : X ⟶ base p} (y : SchemeHomOver (genPt p) f) :
    SchemeHomOver (barPt A ≫ shPt A) (RelativeGroupLaw.baseChangeStr Λ.shStr f) :=
  RelativeGroupLaw.baseChangePointOfBase Λ.shStr (castOver Λ.barPt_shPt_shStr.symm y)

end LevelData

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

structure NeronExtension (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) : Type 1 where

  Nfull : Scheme.{0}

  gN : Nfull ⟶ shBase A

  LN : RelativeGroupLaw ↥(shRing A) gN

  commN : LN.IsCommutative

  hN : ∀ [IsDedekindDomain ↥(shRing A)], NeronModelPropertyBundle ↥(shRing A) ↥(invField A) gN

  openImm : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) gN

  openImm_isOpenImmersion : IsOpenImmersion openImm.1

  openImm_mul : ∀ {T : Scheme.{0}} (s : T ⟶ shBase A)
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).mul s x y) openImm =
        LN.mul s (NeronModelInfra.schemeHomOverComp x openImm) (NeronModelInfra.schemeHomOverComp y openImm)

  openImm_pts_surjective : ∀ y : SchemeHomOver (barPt A ≫ shPt A) gN,
      ∃ x : JZero (N₀ * p), NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) openImm = y

  specN : SchemeHomOver (shPt A) gN → componentGroup O.width

  specN_mul : ∀ s s' : SchemeHomOver (shPt A) gN, specN (LN.mul (shPt A) s s') = specN s + specN s'

  specN_surjective : Function.Surjective specN

  specN_eq_zero_iff : ∀ s : SchemeHomOver (shPt A) gN,
      specN s = 0 ↔ ∃ s₀ : SchemeHomOver Λ.σA O.g, NeronModelInfra.schemeHomOverComp (Λ.shLift s₀) openImm = s

  comp_eq_specN : ∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver (shPt A) gN),
      (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))) openImm).1 = barPt A ≫ s.1 →
        O.comp x = specN s

namespace NeronExtension

variable {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ}

abbrev ptsN (F : O.NeronExtension) (x : JZero (N₀ * p)) : SchemeHomOver (barPt A ≫ shPt A) F.gN :=
  NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) F.openImm

def ExtN (F : O.NeronExtension) (x : JZero (N₀ * p)) : Prop :=
  ∃ s : SchemeHomOver (shPt A) F.gN, (F.ptsN x).1 = barPt A ≫ s.1

def finPts (F : O.NeronExtension) (m : ℕ) : AddSubgroup (JZero (N₀ * p)) :=
  AddSubgroup.closure {x | x ∈ jZeroTorsion (N₀ * p) m ∧ F.ExtN x}

end NeronExtension

end JZeroNeronObjectAtP

end ModularCurve

end
