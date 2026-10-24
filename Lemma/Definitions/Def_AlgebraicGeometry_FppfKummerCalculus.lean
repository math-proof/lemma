import Lemma.Definitions.Def_AlgebraicGeometry_FppfH0Identification
import Lemma.Definitions.Def_AlgebraicGeometry_FppfKummerProp17

universe w' w v u

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

theorem natCard_cohomology_eq_one_of_isZero {Z : Sheaf J AddCommGrpCat.{w}} (hZ : IsZero Z)
    (n : ℕ) : Nat.card (Z.H n) = 1 := by
  haveI := Sheaf.subsingleton_H_of_isZero hZ n
  exact Nat.card_of_subsingleton 0

theorem cohomologyδ_injective_of_subsingleton {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₀)) :
    Function.Injective (cohomologyδ hS n₀ n₁ h) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := (cohomology_exact_three hS n₀ n₁ h x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

theorem cohomologyδ_surjective_of_subsingleton {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₁)) :
    Function.Surjective (cohomologyδ hS n₀ n₁ h) := fun y =>
  (cohomology_exact_one hS n₀ n₁ h y).mp (Subsingleton.elim _ _)

theorem cohomologyδ_bijective_of_subsingleton {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁)) :
    Function.Bijective (cohomologyδ hS n₀ n₁ h) :=
  ⟨cohomologyδ_injective_of_subsingleton hS n₀ n₁ h h₀,
    cohomologyδ_surjective_of_subsingleton hS n₀ n₁ h h₁⟩

theorem cohomologyδ_ker_eq_range {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyδ hS n₀ n₁ h).ker = (cohomologyMap S.g n₀).range :=
  (cohomology_exact_three hS n₀ n₁ h).addMonoidHom_ker_eq

theorem cohomologyMap_ker_eq_cohomologyδ_range {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyMap S.f n₁).ker = (cohomologyδ hS n₀ n₁ h).range :=
  (cohomology_exact_one hS n₀ n₁ h).addMonoidHom_ker_eq

noncomputable def cohomologyDimensionShiftEquiv {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁)) :
    S.X₃.H n₀ ≃+ S.X₁.H n₁ :=
  AddEquiv.ofBijective (cohomologyδ hS n₀ n₁ h)
    (cohomologyδ_bijective_of_subsingleton hS n₀ n₁ h h₀ h₁)

@[simp]
lemma cohomologyDimensionShiftEquiv_apply {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁)) (x : S.X₃.H n₀) :
    cohomologyDimensionShiftEquiv hS n₀ n₁ h h₀ h₁ x = cohomologyδ hS n₀ n₁ h x := rfl

theorem natCard_cohomology_eq_of_subsingleton {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁)) :
    Nat.card (S.X₃.H n₀) = Nat.card (S.X₁.H n₁) :=
  Nat.card_eq_of_bijective _ (cohomologyδ_bijective_of_subsingleton hS n₀ n₁ h h₀ h₁)

theorem natCard_cohomology_le_lower {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₀)) [Finite (S.X₁.H n₁)] :
    Nat.card (S.X₃.H n₀) ≤ Nat.card (S.X₁.H n₁) :=
  Nat.card_le_card_of_injective _ (cohomologyδ_injective_of_subsingleton hS n₀ n₁ h hvanish)

theorem natCard_cohomology_le_upper {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₁)) [Finite (S.X₃.H n₀)] :
    Nat.card (S.X₁.H n₁) ≤ Nat.card (S.X₃.H n₀) :=
  Nat.card_le_card_of_surjective _ (cohomologyδ_surjective_of_subsingleton hS n₀ n₁ h hvanish)

noncomputable def cohomologyCokerEquiv {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₁)) :
    (S.X₃.H n₀ ⧸ (cohomologyMap S.g n₀).range) ≃+ S.X₁.H n₁ :=
  (QuotientAddGroup.quotientAddEquivOfEq (cohomologyδ_ker_eq_range hS n₀ n₁ h).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (cohomologyδ_surjective_of_subsingleton hS n₀ n₁ h hvanish))

lemma cohomologyCokerEquiv_mk {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₁)) (x : S.X₃.H n₀) :
    cohomologyCokerEquiv hS n₀ n₁ h hvanish (QuotientAddGroup.mk x) =
      cohomologyδ hS n₀ n₁ h x := rfl

noncomputable def cohomologyKerEquiv {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₀)) :
    S.X₃.H n₀ ≃+ (cohomologyMap S.f n₁).ker :=
  (AddMonoidHom.ofInjective (cohomologyδ_injective_of_subsingleton hS n₀ n₁ h hvanish)).trans
    (AddEquiv.addSubgroupCongr (cohomologyMap_ker_eq_cohomologyδ_range hS n₀ n₁ h).symm)

lemma cohomologyKerEquiv_apply_coe {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₀)) (x : S.X₃.H n₀) :
    (cohomologyKerEquiv hS n₀ n₁ h hvanish x : S.X₁.H n₁) = cohomologyδ hS n₀ n₁ h x := rfl

theorem cohomology_subsingleton_dimensionShift {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁))
    (h₃ : Subsingleton (S.X₃.H n₀)) :
    Subsingleton (S.X₁.H n₁) :=
  haveI := h₃
  (cohomologyDimensionShiftEquiv hS n₀ n₁ h h₀ h₁).symm.toEquiv.subsingleton

open ZeroObject in

theorem satGate_zeroSES_delta_bijective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective
      (cohomologyδ (biprodSES_shortExact (0 : Sheaf J AddCommGrpCat.{w}) 0) n₀ n₁ h) :=
  cohomologyδ_bijective_of_subsingleton _ n₀ n₁ h
    (Sheaf.subsingleton_H_of_isZero
      ((biprod_isZero_iff _ _).mpr ⟨isZero_zero _, isZero_zero _⟩) n₀)
    (Sheaf.subsingleton_H_of_isZero
      ((biprod_isZero_iff _ _).mpr ⟨isZero_zero _, isZero_zero _⟩) n₁)

open ZeroObject in

theorem satGate_zeroSES_natCard_eq (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Nat.card ((biprodSES (0 : Sheaf J AddCommGrpCat.{w}) 0).X₃.H n₀) =
      Nat.card ((biprodSES (0 : Sheaf J AddCommGrpCat.{w}) 0).X₁.H n₁) :=
  Nat.card_eq_of_bijective _ (satGate_zeroSES_delta_bijective n₀ n₁ h)

open ZeroObject in

theorem satGate_zeroSES_consistency (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective
        (cohomologyδ (biprodSES_shortExact (0 : Sheaf J AddCommGrpCat.{w}) 0) n₀ n₁ h) ∧
      ∀ x : (biprodSES (0 : Sheaf J AddCommGrpCat.{w}) 0).X₃.H n₀,
        cohomologyδ (biprodSES_shortExact (0 : Sheaf J AddCommGrpCat.{w}) 0) n₀ n₁ h x = 0 :=
  ⟨satGate_zeroSES_delta_bijective n₀ n₁ h,
    fun x => biprodSES_delta_apply_eq_zero 0 0 n₀ n₁ h x⟩

end GenericSite

section FppfSite

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

theorem fppf_delta_injective_of_subsingleton
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₀)) :
    Function.Injective (cohomologyδ hS n₀ n₁ h) :=
  cohomologyδ_injective_of_subsingleton hS n₀ n₁ h hvanish

theorem fppf_delta_surjective_of_subsingleton
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₁)) :
    Function.Surjective (cohomologyδ hS n₀ n₁ h) :=
  cohomologyδ_surjective_of_subsingleton hS n₀ n₁ h hvanish

theorem fppf_delta_bijective_of_subsingleton
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁)) :
    Function.Bijective (cohomologyδ hS n₀ n₁ h) :=
  cohomologyδ_bijective_of_subsingleton hS n₀ n₁ h h₀ h₁

noncomputable def fppfDimensionShiftEquiv
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁)) :
    S.X₃.H n₀ ≃+ S.X₁.H n₁ :=
  cohomologyDimensionShiftEquiv hS n₀ n₁ h h₀ h₁

theorem fppf_natCard_eq_of_subsingleton
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (S.X₂.H n₀)) (h₁ : Subsingleton (S.X₂.H n₁)) :
    Nat.card (S.X₃.H n₀) = Nat.card (S.X₁.H n₁) :=
  natCard_cohomology_eq_of_subsingleton hS n₀ n₁ h h₀ h₁

theorem fppf_natCard_le_lower
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₀)) [Finite (S.X₁.H n₁)] :
    Nat.card (S.X₃.H n₀) ≤ Nat.card (S.X₁.H n₁) :=
  natCard_cohomology_le_lower hS n₀ n₁ h hvanish

theorem fppf_natCard_le_upper
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₁)) [Finite (S.X₃.H n₀)] :
    Nat.card (S.X₁.H n₁) ≤ Nat.card (S.X₃.H n₀) :=
  natCard_cohomology_le_upper hS n₀ n₁ h hvanish

noncomputable def fppfCokerEquiv
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₁)) :
    (S.X₃.H n₀ ⧸ (cohomologyMap S.g n₀).range) ≃+ S.X₁.H n₁ :=
  cohomologyCokerEquiv hS n₀ n₁ h hvanish

noncomputable def fppfKerEquiv
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hvanish : Subsingleton (S.X₂.H n₀)) :
    S.X₃.H n₀ ≃+ (cohomologyMap S.f n₁).ker :=
  cohomologyKerEquiv hS n₀ n₁ h hvanish

open ZeroObject in

theorem fppf_satGate_zeroSES_delta_bijective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective
      (cohomologyδ
        (biprodSES_shortExact (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) 0) n₀ n₁ h) :=
  satGate_zeroSES_delta_bijective n₀ n₁ h

end WithLocalInstances

end FppfSite

section KummerConsumer

open AlgebraicGeometry FppfKummerSES

variable (p : ℕ)

theorem kummer_delta_surjective_of_pic_trivial (hp : p ≠ 0)
    (hH1Gm : Subsingleton (FppfH GmAbelianSheafLifted.{u} 1)) :
    Function.Surjective (cohomologyδ (kummerSES_shortExact.{u} p hp) 0 1 rfl) :=
  fppf_delta_surjective_of_subsingleton (kummerSES_shortExact.{u} p hp) 0 1 rfl hH1Gm

noncomputable def kummerH1CokerEquiv (hp : p ≠ 0)
    (hH1Gm : Subsingleton (FppfH GmAbelianSheafLifted.{u} 1)) :
    (FppfH GmAbelianSheafLifted.{u} 0 ⧸ (cohomologyMap (gmPowSelf.{u} p) 0).range) ≃+
      FppfH (muPAbelianSheafLifted.{u} p) 1 :=
  fppfCokerEquiv (kummerSES_shortExact.{u} p hp) 0 1 rfl hH1Gm

theorem kummer_natCard_h1_eq_coker (hp : p ≠ 0)
    (hH1Gm : Subsingleton (FppfH GmAbelianSheafLifted.{u} 1)) :
    Nat.card (FppfH (muPAbelianSheafLifted.{u} p) 1) =
      Nat.card
        (FppfH GmAbelianSheafLifted.{u} 0 ⧸ (cohomologyMap (gmPowSelf.{u} p) 0).range) :=
  (Nat.card_congr (kummerH1CokerEquiv p hp hH1Gm).toEquiv).symm

theorem kummer_subsingleton_of_gm_subsingleton (hp : p ≠ 0) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₀ : Subsingleton (FppfH GmAbelianSheafLifted.{u} n₀))
    (h₁ : Subsingleton (FppfH GmAbelianSheafLifted.{u} n₁)) :
    Subsingleton (FppfH (muPAbelianSheafLifted.{u} p) n₁) :=
  cohomology_subsingleton_dimensionShift (kummerSES_shortExact.{u} p hp) n₀ n₁ h h₀ h₁ h₀

end KummerConsumer

end FppfCohomologyLES

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace FppfBigSiteH0Gm

open CategoryTheory AlgebraicGeometry Limits Opposite
open FppfCohomologyLES FppfRepresentableGroupSchemeSheaf FppfKummerSES

section GenericSiteNaturality

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  [(constantSheaf J AddCommGrpCat.{w}).Additive]

theorem sheafHZeroSectionsAddEquiv_apply {T : C} (hT : IsTerminal T)
    (G : Sheaf J AddCommGrpCat.{w}) (x : G.H 0) :
    EtaleCohomologyLES.sheafHZeroSectionsAddEquiv hT G x =
      Scheme.homULiftIntAddEquiv.{w} (G.obj.obj (op T))
        ((constantSheafAdj J AddCommGrpCat.{w} hT).homAddEquiv
          (AddCommGrpCat.of (ULift.{w} ℤ)) G (cohomologyZeroAddEquivHom G x)) :=
  rfl

theorem sheafHZeroSectionsAddEquiv_naturality {T : C} (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (x : F.H 0) :
    EtaleCohomologyLES.sheafHZeroSectionsAddEquiv hT G (cohomologyMap φ 0 x) =
      φ.hom.app (op T) (EtaleCohomologyLES.sheafHZeroSectionsAddEquiv hT F x) := by
  rw [sheafHZeroSectionsAddEquiv_apply, sheafHZeroSectionsAddEquiv_apply,
    cohomologyZeroAddEquivHom_naturality φ x, Adjunction.homAddEquiv_naturality_right]
  exact Scheme.homULiftIntAddEquiv_naturality _ _

theorem sheafHZeroSectionsAddEquiv_symm_naturality {T : C} (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (s : F.obj.obj (op T)) :
    (EtaleCohomologyLES.sheafHZeroSectionsAddEquiv hT G).symm (φ.hom.app (op T) s) =
      cohomologyMap φ 0 ((EtaleCohomologyLES.sheafHZeroSectionsAddEquiv hT F).symm s) := by
  apply (EtaleCohomologyLES.sheafHZeroSectionsAddEquiv hT G).injective
  rw [AddEquiv.apply_symm_apply, sheafHZeroSectionsAddEquiv_naturality,
    AddEquiv.apply_symm_apply]

end GenericSiteNaturality

section FppfBigSite

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

theorem fppfHZeroSectionsAddEquiv_naturality {T : Scheme.{u}} (hT : IsTerminal T)
    {F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (φ : F ⟶ G) (x : FppfH F 0) :
    EtaleCohomologyLES.fppfHZeroSectionsAddEquiv hT G (cohomologyMap φ 0 x) =
      φ.hom.app (op T) (EtaleCohomologyLES.fppfHZeroSectionsAddEquiv hT F x) :=
  sheafHZeroSectionsAddEquiv_naturality hT φ x

end WithLocalInstances

def bigSiteH0SectionsAddEquiv (F : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    FppfH F 0 ≃+ F.obj.obj (op (Spec (CommRingCat.of ℤ))) :=
  EtaleCohomologyLES.fppfHZeroSectionsAddEquiv specZIsTerminal F

theorem bigSiteH0SectionsAddEquiv_naturality
    {F G : Sheaf Scheme.fppfTopology.{0} Ab.{1}} (φ : F ⟶ G) (x : FppfH F 0) :
    bigSiteH0SectionsAddEquiv G (cohomologyMap φ 0 x) =
      φ.hom.app (op (Spec (CommRingCat.of ℤ))) (bigSiteH0SectionsAddEquiv F x) :=
  fppfHZeroSectionsAddEquiv_naturality specZIsTerminal φ x

theorem bigSiteH0SectionsAddEquiv_symm_naturality
    {F G : Sheaf Scheme.fppfTopology.{0} Ab.{1}} (φ : F ⟶ G)
    (s : F.obj.obj (op (Spec (CommRingCat.of ℤ)))) :
    (bigSiteH0SectionsAddEquiv G).symm (φ.hom.app (op (Spec (CommRingCat.of ℤ))) s) =
      cohomologyMap φ 0 ((bigSiteH0SectionsAddEquiv F).symm s) :=
  sheafHZeroSectionsAddEquiv_symm_naturality specZIsTerminal φ s

end FppfBigSite

section GmInstantiation

def gammaSpecZUnitsMulEquiv :
    ((Γ(Spec (CommRingCat.of ℤ), ⊤) : Type 0))ˣ ≃* ℤˣ :=
  (GmSectionsMulEquiv (Spec (CommRingCat.of ℤ))).symm.trans gateGmSectionsSpecZ

def gmH0AddEquivIntUnits :
    FppfH GmAbelianSheafLifted.{0} 0 ≃+ Additive ℤˣ :=
  ((bigSiteH0SectionsAddEquiv GmAbelianSheafLifted.{0}).trans
    ((gmLiftedSectionsAddEquiv (Spec (CommRingCat.of ℤ))).trans AddEquiv.ulift)).trans
    (MulEquiv.toAdditive gammaSpecZUnitsMulEquiv)

theorem gmH0AddEquivIntUnits_apply (x : FppfH GmAbelianSheafLifted.{0} 0) :
    gmH0AddEquivIntUnits x =
      Additive.ofMul (gammaSpecZUnitsMulEquiv (gmLiftedSectionUnit
        (bigSiteH0SectionsAddEquiv GmAbelianSheafLifted.{0} x))) :=
  rfl

theorem natCard_gmH0_eq_two : Nat.card (FppfH GmAbelianSheafLifted.{0} 0) = 2 := by
  rw [Nat.card_congr gmH0AddEquivIntUnits.toEquiv,
    Nat.card_congr (Additive.toMul (α := ℤˣ))]
  exact natCard_intUnits

theorem natCard_gmH0_ne_zero : Nat.card (FppfH GmAbelianSheafLifted.{0} 0) ≠ 0 := by
  rw [natCard_gmH0_eq_two]; omega

theorem gate_gmH0_nontrivial : Nontrivial (FppfH GmAbelianSheafLifted.{0} 0) := by
  haveI : Nontrivial (Additive ℤˣ) :=
    ⟨Additive.ofMul 1, Additive.ofMul (-1), fun h =>
      absurd (Additive.ofMul.injective h) (by decide)⟩
  exact gmH0AddEquivIntUnits.toEquiv.nontrivial

end GmInstantiation

section MuPInstantiation

theorem gmH0AddEquivIntUnits_cohomologyMap_gmPowSelf (p : ℕ)
    (x : FppfH GmAbelianSheafLifted.{0} 0) :
    gmH0AddEquivIntUnits (cohomologyMap (gmPowSelf.{0} p) 0 x) =
      Additive.ofMul ((gmH0AddEquivIntUnits x).toMul ^ p) := by
  rw [gmH0AddEquivIntUnits_apply, gmH0AddEquivIntUnits_apply,
    bigSiteH0SectionsAddEquiv_naturality (gmPowSelf.{0} p) x]
  exact congrArg Additive.ofMul
    (map_pow gammaSpecZUnitsMulEquiv
      (gmLiftedSectionUnit (bigSiteH0SectionsAddEquiv GmAbelianSheafLifted.{0} x)) p)

theorem cohomologyMap_gmPowSelf_eq_zero_iff (p : ℕ)
    (x : FppfH GmAbelianSheafLifted.{0} 0) :
    cohomologyMap (gmPowSelf.{0} p) 0 x = 0 ↔
      (gmH0AddEquivIntUnits x).toMul ^ p = 1 := by
  constructor
  · intro h
    have h2 : gmH0AddEquivIntUnits (cohomologyMap (gmPowSelf.{0} p) 0 x) = 0 := by
      rw [h, map_zero]
    rw [gmH0AddEquivIntUnits_cohomologyMap_gmPowSelf] at h2
    exact ofMul_eq_zero.mp h2
  · intro h
    apply gmH0AddEquivIntUnits.injective
    rw [gmH0AddEquivIntUnits_cohomologyMap_gmPowSelf, h, ofMul_one, map_zero]

theorem mem_cohomologyMap_gmPowSelf_ker_iff (p : ℕ)
    (x : FppfH GmAbelianSheafLifted.{0} 0) :
    x ∈ (cohomologyMap (gmPowSelf.{0} p) 0).ker ↔
      (gmH0AddEquivIntUnits x).toMul ∈ (powMonoidHom p : ℤˣ →* ℤˣ).ker := by
  rw [AddMonoidHom.mem_ker, MonoidHom.mem_ker, powMonoidHom_apply]
  exact cohomologyMap_gmPowSelf_eq_zero_iff p x

def muPH0EquivIntUnitsPthTorsion (p : ℕ) (hp : p ≠ 0) :
    FppfH (muPAbelianSheafLifted.{0} p) 0 ≃ ((powMonoidHom p : ℤˣ →* ℤˣ).ker) :=
  (kummerKernelH0AddEquiv.{0} p hp).toEquiv.trans
    { toFun := fun x =>
        ⟨(gmH0AddEquivIntUnits (x : FppfH GmAbelianSheafLifted.{0} 0)).toMul,
          (mem_cohomologyMap_gmPowSelf_ker_iff p _).mp x.2⟩
      invFun := fun u =>
        ⟨gmH0AddEquivIntUnits.symm (Additive.ofMul (u : ℤˣ)),
          (mem_cohomologyMap_gmPowSelf_ker_iff p _).mpr (by
            rw [AddEquiv.apply_symm_apply, toMul_ofMul]; exact u.2)⟩
      left_inv := fun x => Subtype.ext (by
        show gmH0AddEquivIntUnits.symm (Additive.ofMul
          (Additive.toMul (gmH0AddEquivIntUnits
            (x : FppfH GmAbelianSheafLifted.{0} 0)))) =
          (x : FppfH GmAbelianSheafLifted.{0} 0)
        rw [ofMul_toMul, AddEquiv.symm_apply_apply])
      right_inv := fun u => Subtype.ext (by
        show Additive.toMul (gmH0AddEquivIntUnits (gmH0AddEquivIntUnits.symm
            (Additive.ofMul (u : ℤˣ)))) = (u : ℤˣ)
        rw [AddEquiv.apply_symm_apply, toMul_ofMul]) }

theorem muPH0EquivIntUnitsPthTorsion_coe (p : ℕ) (hp : p ≠ 0)
    (x : FppfH (muPAbelianSheafLifted.{0} p) 0) :
    (muPH0EquivIntUnitsPthTorsion p hp x : ℤˣ) =
      (gmH0AddEquivIntUnits (cohomologyMap (kummerSES.{0} p).f 0 x)).toMul := by
  have h : (muPH0EquivIntUnitsPthTorsion p hp x : ℤˣ) =
      (gmH0AddEquivIntUnits ((kummerKernelH0AddEquiv.{0} p hp x :
        (cohomologyMap (gmPowSelf.{0} p) 0).ker) :
          FppfH GmAbelianSheafLifted.{0} 0)).toMul := rfl
  rw [h, kummerKernelH0AddEquiv_apply_coe]

theorem natCard_muPH0 (p : ℕ) (hp : p.Prime) :
    Nat.card (FppfH (muPAbelianSheafLifted.{0} p) 0) = if p = 2 then 2 else 1 := by
  rw [Nat.card_congr (muPH0EquivIntUnitsPthTorsion p hp.ne_zero)]
  exact natCard_intUnits_pthTorsion p hp

theorem gate_muPH0_two : Nat.card (FppfH (muPAbelianSheafLifted.{0} 2) 0) = 2 := by
  rw [natCard_muPH0 2 Nat.prime_two]; norm_num

theorem gate_muPH0_three : Nat.card (FppfH (muPAbelianSheafLifted.{0} 3) 0) = 1 := by
  rw [natCard_muPH0 3 Nat.prime_three]; norm_num

end MuPInstantiation

section MazurGates

theorem kummer_h1_card_eq_h0_card_of_pic_trivial_specZ (p : ℕ) (hp : p ≠ 0)
    (hH1Gm : Nat.card (FppfH GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfH (muPAbelianSheafLifted.{0} p) 1) =
      Nat.card (FppfH (muPAbelianSheafLifted.{0} p) 0) :=
  kummer_h1_card_eq_h0_card_of_pic_trivial p hp hH1Gm natCard_gmH0_ne_zero

theorem kummer_h1_card_value_of_pic_trivial (p : ℕ) (hp : p.Prime)
    (hH1Gm : Nat.card (FppfH GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfH (muPAbelianSheafLifted.{0} p) 1) = if p = 2 then 2 else 1 := by
  rw [kummer_h1_card_eq_h0_card_of_pic_trivial_specZ p hp.ne_zero hH1Gm]
  exact natCard_muPH0 p hp

theorem kummer_h1_card_eq_card_intUnits_modPthPowers_of_pic_trivial (p : ℕ) (hp : p.Prime)
    (hH1Gm : Nat.card (FppfH GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfH (muPAbelianSheafLifted.{0} p) 1) =
      Nat.card (ℤˣ ⧸ (powMonoidHom p : ℤˣ →* ℤˣ).range) := by
  rw [kummer_h1_card_value_of_pic_trivial p hp hH1Gm,
    natCard_intUnits_modPthPowers p hp]

end MazurGates

end FppfBigSiteH0Gm
