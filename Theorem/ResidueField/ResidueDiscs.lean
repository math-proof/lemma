module

public import Theorem.Scheme.RegularProlongation
public import Theorem.AlgEquiv.SemistableChartsComap

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace Scheme.RegularProlongation

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

section ResAut

variable (R : RegularProlongation A F Fbar) (τ : F ≃ₐ[L] F) (hτ : ∀ f : F, τ f ∈ R.integers ↔ f ∈ R.integers)


@[simp] public theorem coe_integersEquiv (x : R.integers) : (R.integersEquiv τ hτ x : F) = τ x := rfl

include hτ in

public theorem mem_ker_residue_iff_of_equiv (x : R.integers) :
    R.integersEquiv τ hτ x ∈ RingHom.ker R.residue ↔ x ∈ RingHom.ker R.residue := by
  rw [R.ker_residue, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  exact (MulEquiv.isUnit_map (R.integersEquiv τ hτ).toMulEquiv).not


public theorem resAutRingEquiv_residue (f : R.integers) :
    R.resAutRingEquiv τ hτ (R.residue f) = R.residue (R.integersEquiv τ hτ f) := by
  simp only [resAutRingEquiv, RingEquiv.trans_apply]
  have h1 : R.residueEquiv.symm (R.residue f) = Ideal.Quotient.mk _ f := by
    apply R.residueEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [h1]
  rfl


public theorem resAut_residue (f : R.integers) :
    R.resAut τ hτ (R.residue f) = R.residue ⟨τ f, (hτ f).mpr f.2⟩ :=
  R.resAutRingEquiv_residue τ hτ f

end ResAut

section Disc

variable (R : RegularProlongation A F Fbar)


public theorem mem_smulDisc_iff (D : Set (Place L F)) (P : Place L F) : P ∈ smulDisc τ D ↔ τ⁻¹ • P ∈ D := Iff.rfl

omit [Algebra (ResidueField A) Fbar] in

public theorem smul_mem_smulDisc_iff (D : Set (Place L F)) (P : Place L F) : τ • P ∈ smulDisc τ D ↔ P ∈ D := by
  rw [mem_smulDisc_iff, inv_smul_smul]

variable (hτ : ∀ f : F, τ f ∈ R.integers ↔ f ∈ R.integers)

include hτ in

public theorem symm_mem_integers_iff (f : F) : τ.symm f ∈ R.integers ↔ f ∈ R.integers := by
  rw [← hτ (τ.symm f), AlgEquiv.apply_symm_apply]


public theorem resAut_symm_mul :
    R.resAut τ.symm (R.symm_mem_integers_iff τ hτ) * R.resAut τ hτ = 1 := by
  ext x
  obtain ⟨f, rfl⟩ := R.residue_surjective x
  rw [AlgEquiv.mul_apply, resAut_residue, resAut_residue, AlgEquiv.one_apply]
  congr 1
  exact Subtype.ext (τ.symm_apply_apply (f : F))


public theorem residue_symm_eq (f : R.integers) :
    R.resAut τ hτ (R.residue ⟨τ.symm f, (R.symm_mem_integers_iff τ hτ f).mpr f.2⟩) = R.residue f := by
  rw [resAut_residue]
  congr 1
  exact Subtype.ext (τ.apply_symm_apply (f : F))

include hτ in

public theorem isDiscCoord_smul {Q : Place (ResidueField A) Fbar} {D : Set (Place L F)} {z : F}
    (h : R.IsDiscCoord Q D z) : R.IsDiscCoord (R.resAut τ hτ • Q) (smulDisc τ D) (τ z) := by
  obtain ⟨hD, hz, hord, hbij, het, hup⟩ := h
  refine ⟨?_, (hτ z).mpr hz, ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨hr, hm, hv⟩ := hD _ hP
    refine ⟨(Place.Transport.isRational_smul_iff τ⁻¹ P).mp hr, ?_, ?_⟩
    · rwa [Place.Transport.mem_inv_smul_iff] at hm
    · rwa [← Place.Transport.evalAt_smul τ _ hr, smul_inv_smul] at hv
  · rw [← hord, ← Place.ord_smul (R.resAut τ hτ) Q (R.residue ⟨z, hz⟩), resAut_residue]
  · intro c hc
    obtain ⟨P, ⟨hP, hPc⟩, huniq⟩ := hbij c hc
    refine ⟨τ • P, ⟨(smul_mem_smulDisc_iff τ D P).mpr hP, ?_⟩, ?_⟩
    · rw [Place.Transport.evalAt_smul τ P (hD P hP).1, hPc]
    · rintro P' ⟨hP', hP'c⟩
      have hval : (τ⁻¹ • P').evalAt z = c := by
        rw [← Place.Transport.evalAt_smul τ _ (hD _ hP').1, smul_inv_smul]; exact hP'c
      have := huniq (τ⁻¹ • P') ⟨hP', hval⟩
      rw [← this, smul_inv_smul]
  · intro P hP
    have e := het _ hP
    rw [← Place.ord_smul τ (τ⁻¹ • P), smul_inv_smul, map_sub, AlgEquiv.commutes,
      ← Place.Transport.evalAt_smul τ _ (hD _ hP).1, smul_inv_smul] at e
    exact e
  · intro f hf hf0
    have hf' : ∀ P ∈ D, P.ord (τ.symm f) = 0 := by
      intro P hP
      rw [← Place.Transport.ord_smul' τ P f]
      exact hf0 _ ((smul_mem_smulDisc_iff τ D P).mpr hP)
    obtain ⟨c, hc0, hc⟩ := hup (τ.symm f) (by simpa using hf) hf'
    refine ⟨c, hc0, fun P hP => ?_⟩
    rw [← hc _ hP, ← Place.Transport.evalAt_smul τ _ (hD _ hP).1, smul_inv_smul, AlgEquiv.apply_symm_apply]

omit [Algebra (ResidueField A) Fbar] in

public theorem forall_mem_of_forall_mem_smul {D : Set (Place L F)} {f : F}
    (hreg : ∀ w ∈ smulDisc τ D, f ∈ w.toValuationSubring) :
    ∀ w ∈ D, τ.symm f ∈ w.toValuationSubring := by
  intro w hw
  have h := hreg (τ • w) ((smul_mem_smulDisc_iff τ D w).mpr hw)
  rwa [Place.Transport.mem_smul_iff] at h

include hτ in


public theorem pointwiseOn_smul {Q : Place (ResidueField A) Fbar} {D : Set (Place L F)} (h : R.PointwiseOn Q D) :
    R.PointwiseOn (R.resAut τ hτ • Q) (smulDisc τ D) := by
  intro P hP hPr f hf hreg
  set σ := R.resAut τ hτ with hσ
  have hf' : τ.symm f ∈ R.integers := (R.symm_mem_integers_iff τ hτ f).mpr hf
  have hPr' : (τ⁻¹ • P).IsRational := (Place.Transport.isRational_smul_iff τ⁻¹ P).mpr hPr
  obtain ⟨hm₀, h₀, e₀⟩ := h _ hP hPr' (τ.symm f) hf' (forall_mem_of_forall_mem_smul τ hreg)
  have hres : σ (R.residue ⟨τ.symm f, hf'⟩) = R.residue ⟨f, hf⟩ := R.residue_symm_eq τ hτ ⟨f, hf⟩
  have hm : (R.residue ⟨f, hf⟩ : Fbar) ∈ (σ • Q).toValuationSubring := by
    rw [← hres]; exact (Place.Transport.mem_smul_iff' σ Q _).mpr hm₀
  have hev : (τ⁻¹ • P).evalAt (τ.symm f) = P.evalAt f := by
    rw [← Place.Transport.evalAt_smul τ _ hPr', smul_inv_smul, AlgEquiv.apply_symm_apply]
  refine ⟨hm, hev ▸ h₀, ?_⟩
  have e₁ := congrArg (Place.smulResidueAlgEquiv σ Q) e₀
  rw [AlgEquiv.commutes] at e₁
  have hsub : (⟨P.evalAt f, hev ▸ h₀⟩ : A) = ⟨(τ⁻¹ • P).evalAt (τ.symm f), h₀⟩ := Subtype.ext hev.symm
  rw [hsub, e₁, ← Place.Transport.residue_smul σ Q hm₀ (by rw [hres]; exact hm)]
  congr 1
  exact Subtype.ext hres

include hτ in


public theorem degreeOn_smul {Q : Place (ResidueField A) Fbar} {D : Set (Place L F)} (h : R.DegreeOn Q D) :
    R.DegreeOn (R.resAut τ hτ • Q) (smulDisc τ D) := by
  classical
  intro f hf D' hD hD0
  set σ := R.resAut τ hτ with hσ
  let f' : R.integers := ⟨τ.symm f, (R.symm_mem_integers_iff τ hτ f).mpr f.2⟩
  have hres : σ (R.residue f') = R.residue f := R.residue_symm_eq τ hτ f
  have hf' : R.residue f' ≠ 0 := fun h0 => hf (by rw [← hres, h0, map_zero])
  have key := h f' hf' (τ⁻¹ • D') (fun P hP => ?_) (fun P hP => ?_)
  · rw [← hres, Place.ord_smul σ Q (R.residue f'), ← key, Divisor.smul_def,
      Finsupp.sum_mapDomain_index_inj (MulAction.injective (β := Place L F) τ⁻¹)]
  · rw [Divisor.smul_apply, inv_inv, hD (τ • P) ((smul_mem_smulDisc_iff τ D P).mpr hP),
      Place.Transport.ord_smul' τ P]
  · rw [Divisor.smul_apply, inv_inv]
    exact hD0 _ (fun h' => hP ((smul_mem_smulDisc_iff τ D P).mp h'))

include hτ in


public theorem isResidueDisc_smul {Q : Place (ResidueField A) Fbar} {D : Set (Place L F)} {z : F} (h : R.IsResidueDisc Q D z) :
    R.IsResidueDisc (R.resAut τ hτ • Q) (smulDisc τ D) (τ z) :=
  ⟨R.isDiscCoord_smul τ hτ h.1, R.pointwiseOn_smul τ hτ h.2.1, R.degreeOn_smul τ hτ h.2.2⟩

omit [Algebra (ResidueField A) Fbar] in

public theorem smulDisc_symm_smulDisc (D : Set (Place L F)) : smulDisc τ.symm (smulDisc τ D) = D := by
  ext P
  rw [mem_smulDisc_iff, mem_smulDisc_iff, ← mul_smul, ← AlgEquiv.aut_inv, ← mul_inv_rev, inv_mul_cancel, inv_one, one_smul]

include hτ in

public theorem isResidueDisc_symm {Q : Place (ResidueField A) Fbar} {D : Set (Place L F)} {z : F}
    (h : R.IsResidueDisc (R.resAut τ hτ • Q) D z) : R.IsResidueDisc Q (smulDisc τ.symm D) (τ.symm z) := by
  have key := R.isResidueDisc_smul τ.symm (R.symm_mem_integers_iff τ hτ) h
  rwa [← mul_smul, resAut_symm_mul, one_smul] at key

include hτ in

public theorem isDiscFibre_smul_iff (Q : Place (ResidueField A) Fbar) :
    R.IsDiscFibre (R.resAut τ hτ • Q) ↔ R.IsDiscFibre Q := by
  constructor
  · rintro ⟨D, z, h⟩; exact ⟨_, _, R.isResidueDisc_symm τ hτ h⟩
  · rintro ⟨D, z, h⟩; exact ⟨_, _, R.isResidueDisc_smul τ hτ h⟩

include hτ in

public theorem inDiscFibre_smul_iff (Q : Place (ResidueField A) Fbar) (P : Place L F) :
    R.InDiscFibre (R.resAut τ hτ • Q) (τ • P) ↔ R.InDiscFibre Q P := by
  constructor
  · rintro ⟨D, z, h, hP⟩
    refine ⟨_, _, R.isResidueDisc_symm τ hτ h, ?_⟩
    rw [mem_smulDisc_iff, ← AlgEquiv.aut_inv, inv_inv]
    exact hP
  · rintro ⟨D, z, h, hP⟩
    exact ⟨_, _, R.isResidueDisc_smul τ hτ h, (smul_mem_smulDisc_iff τ D P).mpr hP⟩

end Disc

end Scheme.RegularProlongation

end
