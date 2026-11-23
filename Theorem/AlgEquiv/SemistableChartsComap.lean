module

public import Theorem.ValuationSubring.SemistableCharts

public noncomputable section

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise

namespace Place.Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F)

public theorem mem_smul_iff (f : F) : f ∈ (σ • v).toValuationSubring ↔ σ.symm f ∈ v.toValuationSubring := by
  rw [smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    AlgEquiv.aut_inv]


public theorem mem_smul_iff' (f : F) : σ f ∈ (σ • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [mem_smul_iff, AlgEquiv.symm_apply_apply]


public theorem mem_inv_smul_iff (f : F) : f ∈ (σ⁻¹ • v).toValuationSubring ↔ σ f ∈ v.toValuationSubring := by
  rw [mem_smul_iff, AlgEquiv.aut_inv, AlgEquiv.symm_symm]


public theorem ord_smul' (f : F) : (σ • v).ord f = v.ord (σ.symm f) := by
  conv_lhs => rw [← AlgEquiv.apply_symm_apply σ f]
  exact ord_smul σ v (σ.symm f)


public theorem ord_inv_smul (f : F) : (σ⁻¹ • v).ord f = v.ord (σ f) := by
  rw [ord_smul', AlgEquiv.aut_inv, AlgEquiv.symm_symm]


public theorem isRational_smul_iff : (σ • v).IsRational ↔ v.IsRational := by
  unfold IsRational
  have h : (algebraMap K (σ • v).ResidueField) = (smulResidueAlgEquiv σ v).toAlgHom.toRingHom.comp
      (algebraMap K v.ResidueField) := by
    ext a; simp
  rw [h, RingHom.coe_comp]
  constructor
  · intro hs
    have : Function.Surjective ((smulResidueAlgEquiv σ v).symm ∘ ((smulResidueAlgEquiv σ v).toAlgHom.toRingHom
        ∘ algebraMap K v.ResidueField)) := (smulResidueAlgEquiv σ v).symm.surjective.comp hs
    convert this using 1
    ext a; simp
  · intro hs
    exact (smulResidueAlgEquiv σ v).surjective.comp hs


public theorem residue_smul {f : F} (hf : f ∈ v.toValuationSubring) (hf' : σ f ∈ (σ • v).toValuationSubring) :
    IsLocalRing.residue (σ • v).toValuationSubring ⟨σ f, hf'⟩
      = smulResidueAlgEquiv σ v (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩) := by
  have h1 : (⟨σ f, hf'⟩ : (σ • v).toValuationSubring) = smulRingEquiv σ v.toValuationSubring ⟨f, hf⟩ :=
    Subtype.ext rfl
  rw [h1]
  show _ = IsLocalRing.ResidueField.mapEquiv (smulRingEquiv σ v.toValuationSubring) _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl


public theorem evalAt_smul (hv : v.IsRational) (f : F) : (σ • v).evalAt (σ f) = v.evalAt f := by
  by_cases hf : f ∈ v.toValuationSubring
  · have hf' : σ f ∈ (σ • v).toValuationSubring := (mem_smul_iff' σ v f).mpr hf
    rw [(σ • v).evalAt_of_mem hf', residue_smul σ v hf hf', ← v.algebraMap_evalAt hv hf, AlgEquiv.commutes,
      residueInv_algebraMap]
  · have hf' : σ f ∉ (σ • v).toValuationSubring := fun h => hf ((mem_smul_iff' σ v f).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hf, dif_neg hf']


public theorem evalAt_smul_symm (hv : v.IsRational) (f : F) : (σ • v).evalAt f = v.evalAt (σ.symm f) := by
  conv_lhs => rw [← AlgEquiv.apply_symm_apply σ f]
  exact evalAt_smul σ v hv _


public theorem evalAt_symm (hv : v.IsRational) (f : F) : v.evalAt (σ.symm f) = (σ • v).evalAt f :=
  (evalAt_smul_symm σ v hv f).symm


public theorem smul_inv_smul' (P : Place K F) : σ • σ⁻¹ • P = P := smul_inv_smul σ P


public theorem inv_smul_smul' (P : Place K F) : σ⁻¹ • σ • P = P := inv_smul_smul σ P

end Place.Transport

namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)


@[simp] public theorem mem_comapIntegers (f : F) : f ∈ comapIntegers σ C ↔ σ f ∈ C.integers := Iff.rfl


@[simp] public theorem coe_comapIntegersEquiv (x : comapIntegers σ C) : ((comapIntegersEquiv σ C x : C.integers) : F) = σ x := rfl


@[simp] public theorem comapResidue_apply (x : comapIntegers σ C) : comapResidue σ C x = C.residue ⟨σ x, x.2⟩ := rfl


public theorem comapResidue_surjective : Function.Surjective (comapResidue σ C) :=
  C.residue_surjective.comp (comapIntegersEquiv σ C).surjective


public theorem ker_comapResidue : RingHom.ker (comapResidue σ C) = maximalIdeal (comapIntegers σ C) := by
  ext x
  rw [RingHom.mem_ker, comapResidue, RingHom.comp_apply, ← RingHom.mem_ker, C.ker_residue,
    IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  exact (MulEquiv.isUnit_map (comapIntegersEquiv σ C).toMulEquiv).not


public theorem comapResidue_algebraMap (a : A) :
    comapResidue σ C ⟨algebraMap L F a, by rw [mem_comapIntegers, AlgEquiv.commutes]; exact (C.algebraMap_mem_iff a).mpr a.2⟩
      = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
  rw [comapResidue_apply, ← C.residue_algebraMap a]
  congr 1
  exact Subtype.ext (AlgEquiv.commutes σ a)


@[simp] public theorem comap_integers : (C.comap σ).integers = comapIntegers σ C := rfl

@[simp] public theorem mem_comap_integers (f : F) : f ∈ (C.comap σ).integers ↔ σ f ∈ C.integers := Iff.rfl

@[simp] public theorem comap_dom : (C.comap σ).dom = {P | σ • P ∈ C.dom} := rfl

public theorem mem_comap_dom (P : Place L F) : P ∈ (C.comap σ).dom ↔ σ • P ∈ C.dom := Iff.rfl

@[simp] public theorem comap_nodes : (C.comap σ).nodes = C.nodes := rfl

@[simp] public theorem comap_placeMap (P : Place L F) : (C.comap σ).placeMap P = C.placeMap (σ • P) := rfl

@[simp] public theorem comap_residue_apply (x : (C.comap σ).integers) :
    (C.comap σ).residue x = C.residue ⟨σ (x : F), x.2⟩ := rfl

end ComponentChart

namespace Annulus

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  (σ : F ≃ₐ[L] F) (An : Annulus A F)


public theorem evalAt_symm_param {P : Place L F} (hP : σ • P ∈ An.dom) :
    P.evalAt (σ.symm An.param) = (σ • P).evalAt An.param := by
  have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
  rw [Place.Transport.evalAt_smul_symm σ P hrat]


@[simp] public theorem comap_dom : (An.comap σ).dom = {P | σ • P ∈ An.dom} := rfl

public theorem mem_comap_dom (P : Place L F) : P ∈ (An.comap σ).dom ↔ σ • P ∈ An.dom := Iff.rfl

@[simp] public theorem comap_param : (An.comap σ).param = σ.symm An.param := rfl

@[simp] public theorem comap_modulus : (An.comap σ).modulus = An.modulus := rfl

variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]


public theorem IsAttached.comap {C : ComponentChart A F Fbar} {x : Place (ResidueField A) Fbar}
    (h : An.IsAttached C x) : (An.comap σ).IsAttached (C.comap σ) x := by
  obtain ⟨hx, hz, hord, hslope⟩ := h
  have hz' : σ.symm An.param ∈ (C.comap σ).integers := by
    rw [ComponentChart.mem_comap_integers, AlgEquiv.apply_symm_apply]; exact hz
  refine ⟨hx, hz', ?_, ?_⟩
  · rw [ComponentChart.comap_residue_apply]
    convert hord using 3
    exact Subtype.ext (σ.apply_symm_apply An.param)
  · intro f hf hres hordf P hP
    have hres' : C.residue ⟨σ f, hf⟩ ≠ 0 := by rwa [ComponentChart.comap_residue_apply] at hres
    have hordf' : ∀ P₀ ∈ An.dom, P₀.ord (σ f) = 0 := by
      intro P₀ hP₀
      have h := hordf (σ⁻¹ • P₀) (show σ • σ⁻¹ • P₀ ∈ An.dom by rwa [smul_inv_smul])
      rwa [Place.Transport.ord_inv_smul] at h
    have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
    obtain ⟨h, hu⟩ := hslope (σ f) hf hres' hordf' (σ • P) hP
    have key : P.evalAt f * P.evalAt (σ.symm An.param) ^ (-(x.ord ((C.comap σ).residue ⟨f, hf⟩)))
        = (σ • P).evalAt (σ f) * (σ • P).evalAt An.param ^ (-(x.ord (C.residue ⟨σ f, hf⟩))) := by
      rw [Place.Transport.evalAt_smul σ P hrat, Place.Transport.evalAt_symm σ P hrat, ComponentChart.comap_residue_apply]
    refine ⟨key ▸ h, ?_⟩
    convert hu using 1
    exact Subtype.ext key


public theorem IsAttached.of_comap {C : ComponentChart A F Fbar} {x : Place (ResidueField A) Fbar}
    (h : (An.comap σ).IsAttached (C.comap σ) x) : An.IsAttached C x := by
  obtain ⟨hx, hz', hord', hslope'⟩ := h
  have hz : An.param ∈ C.integers := by
    have := hz'; rw [ComponentChart.mem_comap_integers, comap_param, AlgEquiv.apply_symm_apply] at this; exact this
  refine ⟨hx, hz, ?_, ?_⟩
  · rw [ComponentChart.comap_residue_apply] at hord'
    convert hord' using 3
    exact Subtype.ext (σ.apply_symm_apply An.param).symm
  · intro f hf hres hordf P hP
    have hf' : σ.symm f ∈ (C.comap σ).integers := by
      rw [ComponentChart.mem_comap_integers, AlgEquiv.apply_symm_apply]; exact hf
    have hres' : (C.comap σ).residue ⟨σ.symm f, hf'⟩ ≠ 0 := by
      rw [ComponentChart.comap_residue_apply]
      convert hres using 2
      exact Subtype.ext (σ.apply_symm_apply f)
    have hordf' : ∀ Q ∈ (An.comap σ).dom, Q.ord (σ.symm f) = 0 := by
      intro Q hQ
      rw [← Place.Transport.ord_smul' σ Q f]
      exact hordf (σ • Q) hQ
    have hPQ : σ⁻¹ • P ∈ (An.comap σ).dom := by
      show σ • σ⁻¹ • P ∈ An.dom; rwa [smul_inv_smul]
    have hrat : (σ⁻¹ • P).IsRational := by
      rw [← Place.Transport.isRational_smul_iff σ, smul_inv_smul]; exact (An.mem_dom _ hP).1
    obtain ⟨h, hu⟩ := hslope' (σ.symm f) hf' hres' hordf' (σ⁻¹ • P) hPQ
    have e1 : (σ⁻¹ • P).evalAt (σ.symm f) = P.evalAt f := by
      rw [Place.Transport.evalAt_symm σ _ hrat, smul_inv_smul]
    have e2 : (σ⁻¹ • P).evalAt (An.comap σ).param = P.evalAt An.param := by
      rw [comap_param, Place.Transport.evalAt_symm σ _ hrat, smul_inv_smul]
    have e3 : x.ord ((C.comap σ).residue ⟨σ.symm f, hf'⟩) = x.ord (C.residue ⟨f, hf⟩) := by
      rw [ComponentChart.comap_residue_apply]
      congr 2
      exact Subtype.ext (σ.apply_symm_apply f)
    have key : P.evalAt f * P.evalAt An.param ^ (-(x.ord (C.residue ⟨f, hf⟩)))
        = (σ⁻¹ • P).evalAt (σ.symm f) * (σ⁻¹ • P).evalAt (An.comap σ).param
            ^ (-(x.ord ((C.comap σ).residue ⟨σ.symm f, hf'⟩))) := by
      rw [e1, e2, e3]
    refine ⟨key ▸ h, ?_⟩
    convert hu using 1
    exact Subtype.ext key


public theorem isAttached_comap_iff {C : ComponentChart A F Fbar} {x : Place (ResidueField A) Fbar} :
    (An.comap σ).IsAttached (C.comap σ) x ↔ An.IsAttached C x :=
  ⟨IsAttached.of_comap σ An, IsAttached.comap σ An⟩


public theorem mem_comap_comap_dom (τ : F ≃ₐ[L] F) (P : Place L F) :
    P ∈ ((An.comap σ).comap τ).dom ↔ σ • τ • P ∈ An.dom := Iff.rfl


public theorem comap_comap_param (τ : F ≃ₐ[L] F) : ((An.comap σ).comap τ).param = τ.symm (σ.symm An.param) := rfl


public theorem mem_comap_symm_dom (P : Place L F) : P ∈ ((An.comap σ).comap σ.symm).dom ↔ P ∈ An.dom := by
  rw [mem_comap_comap_dom]
  show σ • σ⁻¹ • P ∈ An.dom ↔ P ∈ An.dom
  rw [smul_inv_smul]


public theorem comap_symm_param : ((An.comap σ).comap σ.symm).param = An.param := by
  rw [comap_comap_param, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]

end Annulus

namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (σ τ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)


public theorem mem_comap_comap_integers (f : F) : f ∈ ((C.comap σ).comap τ).integers ↔ σ (τ f) ∈ C.integers := Iff.rfl


public theorem mem_comap_comap_dom (P : Place L F) : P ∈ ((C.comap σ).comap τ).dom ↔ σ • τ • P ∈ C.dom := Iff.rfl


public theorem comap_comap_placeMap (P : Place L F) : ((C.comap σ).comap τ).placeMap P = C.placeMap (σ • τ • P) := rfl


public theorem mem_comap_symm_integers (f : F) : f ∈ ((C.comap σ).comap σ.symm).integers ↔ f ∈ C.integers := by
  rw [mem_comap_comap_integers, AlgEquiv.apply_symm_apply]


public theorem mem_comap_symm_dom (P : Place L F) : P ∈ ((C.comap σ).comap σ.symm).dom ↔ P ∈ C.dom := by
  rw [mem_comap_comap_dom]
  show σ • σ⁻¹ • P ∈ C.dom ↔ P ∈ C.dom
  rw [smul_inv_smul]


public theorem comap_symm_placeMap (P : Place L F) : ((C.comap σ).comap σ.symm).placeMap P = C.placeMap P := by
  rw [comap_comap_placeMap]
  show C.placeMap (σ • σ⁻¹ • P) = C.placeMap P
  rw [smul_inv_smul]


public theorem comap_symm_residue_apply (f : F) (hf : f ∈ ((C.comap σ).comap σ.symm).integers) (hf' : f ∈ C.integers) :
    ((C.comap σ).comap σ.symm).residue ⟨f, hf⟩ = C.residue ⟨f, hf'⟩ := by
  rw [comap_residue_apply, comap_residue_apply]
  congr 1
  exact Subtype.ext (σ.apply_symm_apply f)

end ComponentChart

end AlgebraicCurve

end
