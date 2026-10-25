import Lemma.AlgebraicCurve.GluedPic0
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise

section Functoriality

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.HasValue.smul {v : Place K F} {f : F} {a : K} (g : SemilinearAut K F)
    (h : v.HasValue f a) : (g • v).HasValue (g • f) (SemilinearAut.baseAut g a) := by
  obtain ⟨hm, hr⟩ := h
  have hmem : g • f ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g f v.toValuationSubring hm
  refine ⟨hmem, ?_⟩
  have hx : (⟨g • f, hmem⟩ : (g • v).toValuationSubring)
      = SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, hm⟩ := by
    ext
    rw [SemilinearAut.coe_smulValuationSubringEquiv_apply]
  rw [hx]
  have hres : residue ((g • v).toValuationSubring)
        (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, hm⟩)
      = SemilinearAut.smulResidueRingEquiv g v (residue v.toValuationSubring ⟨f, hm⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  rw [hres, hr, SemilinearAut.smulResidueRingEquiv_algebraMap]

namespace SemilinearAut

variable (S : Finset (Place K F × Place K F))

def IsNodeStable (g : SemilinearAut K F) : Prop :=
  ∀ s ∈ S, (g • s.1, g • s.2) ∈ S

variable (g : SemilinearAut K F)

def nodePerm (hstab : IsNodeStable S g) : ↥S ≃ ↥S :=
  Equiv.ofBijective
    (fun s => ⟨(g • (s : Place K F × Place K F).1, g • (s : Place K F × Place K F).2),
      hstab _ s.2⟩)
    (Finite.injective_iff_bijective.mp (by
      intro s t hst
      have h1 := congrArg (fun z : ↥S => (z : Place K F × Place K F).1) hst
      have h2 := congrArg (fun z : ↥S => (z : Place K F × Place K F).2) hst
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact MulAction.injective g (by simpa using h1)
      · exact MulAction.injective g (by simpa using h2)))

@[simp]
theorem nodePerm_apply (hstab : IsNodeStable S g) (s : ↥S) :
    (nodePerm S g hstab s : Place K F × Place K F)
      = (g • (s : Place K F × Place K F).1, g • (s : Place K F × Place K F).2) :=
  rfl

theorem nodePerm_symm_apply (hstab : IsNodeStable S g) (t : ↥S) :
    ((nodePerm S g hstab).symm t : Place K F × Place K F)
      = (g⁻¹ • (t : Place K F × Place K F).1, g⁻¹ • (t : Place K F × Place K F).2) := by
  have h := nodePerm_apply S g hstab ((nodePerm S g hstab).symm t)
  rw [Equiv.apply_symm_apply] at h
  refine Prod.ext ?_ ?_
  · rw [eq_inv_smul_iff]
    exact (congrArg Prod.fst h).symm
  · rw [eq_inv_smul_iff]
    exact (congrArg Prod.snd h).symm

theorem IsNodeStable.inv (hstab : IsNodeStable S g) : IsNodeStable S g⁻¹ := by
  intro s hs
  have hsym := nodePerm_symm_apply S g hstab ⟨s, hs⟩
  exact hsym ▸ ((nodePerm S g hstab).symm ⟨s, hs⟩).2

def baseAutUnitsHom : Additive Kˣ →+ Additive Kˣ :=
  AddMonoidHom.mk'
    (fun x => Additive.ofMul (Units.map ((baseAut g : K →+* K) : K →* K) x.toMul))
    (fun x y => by simp)

@[simp]
theorem baseAutUnitsHom_apply (x : Additive Kˣ) :
    baseAutUnitsHom g x
      = Additive.ofMul (Units.map ((baseAut g : K →+* K) : K →* K) x.toMul) :=
  rfl

def gluingMap (hstab : IsNodeStable S g) :
    GluingData K F S →+ GluingData K F S :=
  AddMonoidHom.mk'
    (fun x => (g • x.1, g • x.2.1,
      fun t => baseAutUnitsHom g (x.2.2 ((nodePerm S g hstab).symm t))))
    (fun x y => by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [smul_add]
      · simp [smul_add]
      · funext t
        simp)

@[simp]
theorem gluingMap_apply (hstab : IsNodeStable S g) (x : GluingData K F S) :
    gluingMap S g hstab x = (g • x.1, g • x.2.1,
      fun t => baseAutUnitsHom g (x.2.2 ((nodePerm S g hstab).symm t))) :=
  rfl

theorem gluingMap_mem_admissible (hstab : IsNodeStable S g) {x : GluingData K F S}
    (hx : x ∈ GluingData.admissible S) :
    gluingMap S g hstab x ∈ GluingData.admissible S := by
  obtain ⟨h₁, h₂, hav⟩ := hx
  refine ⟨smul_mem_degZero g h₁, smul_mem_degZero g h₂, fun s hs => ?_⟩
  obtain ⟨hz₁, hz₂⟩ := hav _ (IsNodeStable.inv S g hstab s hs)
  constructor
  · rw [show (gluingMap S g hstab x).1 = g • x.1 from rfl, divisor_smul_apply]
    exact hz₁
  · rw [show (gluingMap S g hstab x).2.1 = g • x.2.1 from rfl, divisor_smul_apply]
    exact hz₂

theorem gluingMap_mem_gluedPrincipal (hstab : IsNodeStable S g) {x : GluingData K F S}
    (hx : GluingData.IsGluedPrincipal S x) :
    GluingData.IsGluedPrincipal S (gluingMap S g hstab x) := by
  obtain ⟨g₁, g₂, a, b, hg₁, hg₂, h₁, h₂, hv, hw⟩ := hx
  refine ⟨g • g₁, g • g₂,
    fun t => Units.map ((baseAut g : K →+* K) : K →* K) (a ((nodePerm S g hstab).symm t)),
    fun t => Units.map ((baseAut g : K →+* K) : K →* K) (b ((nodePerm S g hstab).symm t)),
    by simpa using hg₁, by simpa using hg₂, fun v => ?_, fun v => ?_, fun t => ⟨?_, ?_⟩, ?_⟩
  · rw [show (gluingMap S g hstab x).1 = g • x.1 from rfl, divisor_smul_apply, h₁ (g⁻¹ • v)]
    have h := ord_smul g (g⁻¹ • v) g₁
    rw [smul_inv_smul] at h
    exact h.symm
  · rw [show (gluingMap S g hstab x).2.1 = g • x.2.1 from rfl, divisor_smul_apply,
      h₂ (g⁻¹ • v)]
    have h := ord_smul g (g⁻¹ • v) g₂
    rw [smul_inv_smul] at h
    exact h.symm
  · have hs := (hv ((nodePerm S g hstab).symm t)).1
    have hres := Place.HasValue.smul g hs
    have hc : (((nodePerm S g hstab).symm t : Place K F × Place K F)).1
        = g⁻¹ • (t : Place K F × Place K F).1 :=
      congrArg Prod.fst (nodePerm_symm_apply S g hstab t)
    rw [hc, smul_inv_smul] at hres
    exact hres
  · have hs := (hv ((nodePerm S g hstab).symm t)).2
    have hres := Place.HasValue.smul g hs
    have hc : (((nodePerm S g hstab).symm t : Place K F × Place K F)).2
        = g⁻¹ • (t : Place K F × Place K F).2 :=
      congrArg Prod.snd (nodePerm_symm_apply S g hstab t)
    rw [hc, smul_inv_smul] at hres
    exact hres
  · rw [show (gluingMap S g hstab x).2.2
        = fun t => baseAutUnitsHom g (x.2.2 ((nodePerm S g hstab).symm t)) from rfl, hw]
    funext t
    simp [div_eq_mul_inv]

def admissibleMap (hstab : IsNodeStable S g) :
    ↥(GluingData.admissible S) →+ ↥(GluingData.admissible S) :=
  ((gluingMap S g hstab).domRestrict (GluingData.admissible S)).codRestrict _
    (fun x => gluingMap_mem_admissible S g hstab x.2)

@[simp]
theorem coe_admissibleMap (hstab : IsNodeStable S g) (x : ↥(GluingData.admissible S)) :
    (admissibleMap S g hstab x : GluingData K F S) = gluingMap S g hstab (x : GluingData K F S) :=
  rfl

end SemilinearAut

namespace GluedPic0

open SemilinearAut

variable (S : Finset (Place K F × Place K F)) (g : SemilinearAut K F)

def glueMap (hstab : IsNodeStable S g) : GluedPic0 K F S →+ GluedPic0 K F S :=
  QuotientAddGroup.map _ _ (admissibleMap S g hstab) (by
    rintro x hx
    simp only [AddSubgroup.mem_addSubgroupOf] at hx ⊢
    exact gluingMap_mem_gluedPrincipal S g hstab hx)

@[simp]
theorem glueMap_mk (hstab : IsNodeStable S g) (x : ↥(GluingData.admissible S)) :
    glueMap S g hstab (mk S x) = mk S (admissibleMap S g hstab x) :=
  rfl

theorem toPic0Pair_glueMap (hstab : IsNodeStable S g) (ξ : GluedPic0 K F S) :
    toPic0Pair S (glueMap S g hstab ξ)
      = (g • (toPic0Pair S ξ).1, g • (toPic0Pair S ξ).2) := by
  obtain ⟨x, rfl⟩ := mk_surjective S ξ
  rw [glueMap_mk, toPic0Pair_mk, toPic0Pair_mk]
  refine Prod.ext ?_ ?_
  · rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom]; rfl))
  · rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom]; rfl))

theorem glueMap_nodeUnit (hstab : IsNodeStable S g) (w : ↥S → Additive Kˣ) :
    glueMap S g hstab (nodeUnit S w)
      = nodeUnit S (fun t => baseAutUnitsHom g (w ((nodePerm S g hstab).symm t))) := by
  rw [nodeUnit_apply, nodeUnit_apply, glueMap_mk]
  refine congrArg (mk S) (Subtype.ext ?_)
  rw [coe_admissibleMap]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show g • (0 : Divisor K F) = 0
    exact smul_zero g
  · show g • (0 : Divisor K F) = 0
    exact smul_zero g
  · rfl

end GluedPic0

end Functoriality

end AlgebraicCurve

end
