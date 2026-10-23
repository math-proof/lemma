import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0SliceOps

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace SemilinearAut

variable (S : Finset (Place K F × Place K F)) (g₀ g₁ : SemilinearAut K F)

def IsCrossStable : Prop :=
  ∀ s ∈ S, (g₁ • s.2, g₀ • s.1) ∈ S

variable {S g₀ g₁}

def crossPerm (hstab : IsCrossStable S g₀ g₁) : ↥S ≃ ↥S :=
  Equiv.ofBijective
    (fun s => ⟨(g₁ • (s : Place K F × Place K F).2, g₀ • (s : Place K F × Place K F).1),
      hstab _ s.2⟩)
    (Finite.injective_iff_bijective.mp (by
      intro s t hst
      have h1 := congrArg (fun z : ↥S => (z : Place K F × Place K F).1) hst
      have h2 := congrArg (fun z : ↥S => (z : Place K F × Place K F).2) hst
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact MulAction.injective g₀ (by simpa using h2)
      · exact MulAction.injective g₁ (by simpa using h1)))

@[simp]
theorem crossPerm_apply (hstab : IsCrossStable S g₀ g₁) (s : ↥S) :
    (crossPerm hstab s : Place K F × Place K F)
      = (g₁ • (s : Place K F × Place K F).2, g₀ • (s : Place K F × Place K F).1) :=
  rfl

theorem crossPerm_symm_apply (hstab : IsCrossStable S g₀ g₁) (t : ↥S) :
    ((crossPerm hstab).symm t : Place K F × Place K F)
      = (g₀⁻¹ • (t : Place K F × Place K F).2, g₁⁻¹ • (t : Place K F × Place K F).1) := by
  have h := crossPerm_apply hstab ((crossPerm hstab).symm t)
  rw [Equiv.apply_symm_apply] at h
  refine Prod.ext ?_ ?_
  · rw [eq_inv_smul_iff]
    exact (congrArg Prod.snd h).symm
  · rw [eq_inv_smul_iff]
    exact (congrArg Prod.fst h).symm

theorem smul_symm_snd (hstab : IsCrossStable S g₀ g₁) (t : ↥S) :
    g₁ • ((crossPerm hstab).symm t : Place K F × Place K F).2 = (t : Place K F × Place K F).1 := by
  rw [crossPerm_symm_apply, smul_inv_smul]

theorem smul_symm_fst (hstab : IsCrossStable S g₀ g₁) (t : ↥S) :
    g₀ • ((crossPerm hstab).symm t : Place K F × Place K F).1 = (t : Place K F × Place K F).2 := by
  rw [crossPerm_symm_apply, smul_inv_smul]

theorem crossPerm_symm_eq_of_snd_eq (hstab : IsCrossStable S g₀ g₁)
    (hinj : Set.InjOn Prod.snd (S : Set (Place K F × Place K F)))
    (σ : ↥S ≃ ↥S) (hσ : ∀ t : ↥S, ((σ t : ↥S) : Place K F × Place K F).2 = g₁⁻¹ • (t : Place K F × Place K F).1) :
    (crossPerm hstab).symm = σ := by
  refine Equiv.ext fun t => Subtype.ext (hinj ((crossPerm hstab).symm t).2 (σ t).2 ?_)
  show (((crossPerm hstab).symm t : ↥S) : Place K F × Place K F).2 = ((σ t : ↥S) : Place K F × Place K F).2
  rw [crossPerm_symm_apply, hσ]

theorem crossPerm_symm_eq_of_snd_eq_fst {g₀ : SemilinearAut K F} (hstab : IsCrossStable S g₀ 1)
    (hinj : Set.InjOn Prod.snd (S : Set (Place K F × Place K F)))
    (σ : ↥S ≃ ↥S) (hσ : ∀ t : ↥S, ((σ t : ↥S) : Place K F × Place K F).2 = (t : Place K F × Place K F).1) :
    (crossPerm hstab).symm = σ :=
  crossPerm_symm_eq_of_snd_eq hstab hinj σ fun t => by rw [hσ, inv_one, one_smul]

variable (S g₀ g₁) in

def crossGluingMap (hstab : IsCrossStable S g₀ g₁) :
    GluingData K F S →+ GluingData K F S :=
  AddMonoidHom.mk'
    (fun x => (g₁ • x.2.1, g₀ • x.1,
      fun t => -baseAutUnitsHom g₀ (x.2.2 ((crossPerm hstab).symm t))))
    (fun x y => by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [smul_add]
      · simp [smul_add]
      · funext t
        simp only [Prod.snd_add, Pi.add_apply, map_add, neg_add])

@[simp]
theorem crossGluingMap_apply (hstab : IsCrossStable S g₀ g₁) (x : GluingData K F S) :
    crossGluingMap S g₀ g₁ hstab x = (g₁ • x.2.1, g₀ • x.1,
      fun t => -baseAutUnitsHom g₀ (x.2.2 ((crossPerm hstab).symm t))) :=
  rfl

theorem crossGluingMap_mem_admissible (hstab : IsCrossStable S g₀ g₁) {x : GluingData K F S}
    (hx : x ∈ GluingData.admissible S) :
    crossGluingMap S g₀ g₁ hstab x ∈ GluingData.admissible S := by
  obtain ⟨h₁, h₂, hav⟩ := hx
  refine ⟨smul_mem_degZero g₁ h₂, smul_mem_degZero g₀ h₁, fun t ht => ?_⟩
  obtain ⟨hz₁, hz₂⟩ := hav _ ((crossPerm hstab).symm ⟨t, ht⟩).2
  constructor
  · rw [show (crossGluingMap S g₀ g₁ hstab x).1 = g₁ • x.2.1 from rfl, divisor_smul_apply]
    have h := congrArg Prod.snd (crossPerm_symm_apply hstab ⟨t, ht⟩)
    dsimp only at h
    rw [h] at hz₂
    simpa using hz₂
  · rw [show (crossGluingMap S g₀ g₁ hstab x).2.1 = g₀ • x.1 from rfl, divisor_smul_apply]
    have h := congrArg Prod.fst (crossPerm_symm_apply hstab ⟨t, ht⟩)
    dsimp only at h
    rw [h] at hz₁
    simpa using hz₁

theorem crossGluingMap_mem_gluedPrincipal (hstab : IsCrossStable S g₀ g₁) (hβ : baseAut g₀ = baseAut g₁)
    {x : GluingData K F S} (hx : GluingData.IsGluedPrincipal S x) :
    GluingData.IsGluedPrincipal S (crossGluingMap S g₀ g₁ hstab x) := by
  obtain ⟨f₁, f₂, a, b, hf₁, hf₂, h₁, h₂, hv, hw⟩ := hx
  refine ⟨g₁ • f₂, g₀ • f₁,
    fun t => Units.map ((baseAut g₁ : K →+* K) : K →* K) (b ((crossPerm hstab).symm t)),
    fun t => Units.map ((baseAut g₀ : K →+* K) : K →* K) (a ((crossPerm hstab).symm t)),
    by simpa using hf₂, by simpa using hf₁, fun v => ?_, fun v => ?_, fun t => ⟨?_, ?_⟩, ?_⟩
  · rw [show (crossGluingMap S g₀ g₁ hstab x).1 = g₁ • x.2.1 from rfl, divisor_smul_apply, h₂ (g₁⁻¹ • v)]
    have h := ord_smul g₁ (g₁⁻¹ • v) f₂
    rw [smul_inv_smul] at h
    exact h.symm
  · rw [show (crossGluingMap S g₀ g₁ hstab x).2.1 = g₀ • x.1 from rfl, divisor_smul_apply, h₁ (g₀⁻¹ • v)]
    have h := ord_smul g₀ (g₀⁻¹ • v) f₁
    rw [smul_inv_smul] at h
    exact h.symm
  · have hs := (hv ((crossPerm hstab).symm t)).2
    have hres := Place.HasValue.smul g₁ hs
    rw [smul_symm_snd hstab t] at hres
    exact hres
  · have hs := (hv ((crossPerm hstab).symm t)).1
    have hres := Place.HasValue.smul g₀ hs
    rw [smul_symm_fst hstab t] at hres
    exact hres
  · rw [show (crossGluingMap S g₀ g₁ hstab x).2.2
        = fun t => -baseAutUnitsHom g₀ (x.2.2 ((crossPerm hstab).symm t)) from rfl, hw]
    funext t
    simp [div_eq_mul_inv, hβ]

variable (S g₀ g₁) in

def crossAdmissibleMap (hstab : IsCrossStable S g₀ g₁) :
    ↥(GluingData.admissible S) →+ ↥(GluingData.admissible S) :=
  ((crossGluingMap S g₀ g₁ hstab).domRestrict (GluingData.admissible S)).codRestrict _
    (fun x => crossGluingMap_mem_admissible hstab x.2)

@[simp]
theorem coe_crossAdmissibleMap (hstab : IsCrossStable S g₀ g₁) (x : ↥(GluingData.admissible S)) :
    (crossAdmissibleMap S g₀ g₁ hstab x : GluingData K F S) = crossGluingMap S g₀ g₁ hstab (x : GluingData K F S) :=
  rfl

end SemilinearAut

namespace GluedPic0

open SemilinearAut

variable (S : Finset (Place K F × Place K F)) (g₀ g₁ : SemilinearAut K F)

def crossMap (hstab : IsCrossStable S g₀ g₁) (hβ : baseAut g₀ = baseAut g₁) : GluedPic0 K F S →+ GluedPic0 K F S :=
  QuotientAddGroup.map _ _ (crossAdmissibleMap S g₀ g₁ hstab) (by
    rintro x hx
    simp only [AddSubgroup.mem_addSubgroupOf] at hx ⊢
    exact crossGluingMap_mem_gluedPrincipal hstab hβ hx)

@[simp]
theorem crossMap_mk (hstab : IsCrossStable S g₀ g₁) (hβ : baseAut g₀ = baseAut g₁)
    (x : ↥(GluingData.admissible S)) :
    crossMap S g₀ g₁ hstab hβ (mk S x) = mk S (crossAdmissibleMap S g₀ g₁ hstab x) :=
  rfl

theorem toPic0Pair_crossMap (hstab : IsCrossStable S g₀ g₁) (hβ : baseAut g₀ = baseAut g₁) (ξ : GluedPic0 K F S) :
    toPic0Pair S (crossMap S g₀ g₁ hstab hβ ξ)
      = (g₁ • (toPic0Pair S ξ).2, g₀ • (toPic0Pair S ξ).1) := by
  obtain ⟨x, rfl⟩ := mk_surjective S ξ
  rw [crossMap_mk, toPic0Pair_mk, toPic0Pair_mk]
  refine Prod.ext ?_ ?_
  · rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom]; rfl))
  · rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom]; rfl))

theorem toPic0Pair_crossMap_eq_blockOp (hstab : IsCrossStable S g₀ g₁) (hβ : baseAut g₀ = baseAut g₁) (ξ : GluedPic0 K F S) :
    toPic0Pair S (crossMap S g₀ g₁ hstab hβ ξ) =
      Pic0Pair.blockOp 0 (DistribSMul.toAddMonoidHom (Pic0 K F) g₁)
        (DistribSMul.toAddMonoidHom (Pic0 K F) g₀) 0 (toPic0Pair S ξ) := by
  rw [toPic0Pair_crossMap]
  obtain ⟨c₀, c₁⟩ := toPic0Pair S ξ
  simp [Pic0Pair.blockOp_apply]

theorem crossMap_nodeUnit (hstab : IsCrossStable S g₀ g₁) (hβ : baseAut g₀ = baseAut g₁) (w : ↥S → Additive Kˣ) :
    crossMap S g₀ g₁ hstab hβ (nodeUnit S w)
      = nodeUnit S (fun t => -baseAutUnitsHom g₀ (w ((crossPerm hstab).symm t))) := by
  rw [nodeUnit_apply, nodeUnit_apply, crossMap_mk]
  refine congrArg (mk S) (Subtype.ext ?_)
  rw [coe_crossAdmissibleMap]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show g₁ • (0 : Divisor K F) = 0
    exact smul_zero g₁
  · show g₀ • (0 : Divisor K F) = 0
    exact smul_zero g₀
  · rfl

theorem crossMap_nodeUnit_eq (hstab : IsCrossStable S g₀ g₁) (hβ : baseAut g₀ = baseAut g₁) (w : ↥S → Additive Kˣ) :
    crossMap S g₀ g₁ hstab hβ (nodeUnit S w)
      = nodeUnit S (NodeData.map (-(baseAutUnitsHom g₀ : Additive Kˣ →+ Additive Kˣ))
          (NodeData.perm (crossPerm hstab).symm w)) :=
  crossMap_nodeUnit S g₀ g₁ hstab hβ w

end GluedPic0

end AlgebraicCurve

end
