import Lemma.ValuationSubring.SemistableCharts

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise


namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)

def comapIntegers : ValuationSubring F := C.integers.comap σ.toAlgHom.toRingHom

def comapIntegersEquiv : comapIntegers σ C ≃+* C.integers where
  toFun x := ⟨σ x, x.2⟩
  invFun y := ⟨σ.symm y, by simp [mem_comapIntegers]⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv y := Subtype.ext (σ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul σ (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add σ (x : F) (y : F))

def comapResidue : comapIntegers σ C →+* Fbar := C.residue.comp (comapIntegersEquiv σ C).toRingHom

def comap : ComponentChart A F Fbar where
  integers := comapIntegers σ C
  residue := comapResidue σ C
  dom := {P | σ • P ∈ C.dom}
  nodes := C.nodes
  placeMap P := C.placeMap (σ • P)
  algebraMap_mem_iff x := by
    rw [mem_comapIntegers, AlgEquiv.commutes]; exact C.algebraMap_mem_iff x
  residue_surjective := comapResidue_surjective σ C
  ker_residue := ker_comapResidue σ C
  residue_algebraMap a := comapResidue_algebraMap σ C a
  exists_smul_mem f hf := by
    obtain ⟨c, h, hres⟩ := C.exists_smul_mem (σ f) (by simpa using hf)
    refine ⟨c, by rw [mem_comapIntegers, map_smul]; exact h, ?_⟩
    rw [comapResidue_apply]
    convert hres using 2
    exact Subtype.ext (map_smul σ c f)
  placeMap_not_mem_nodes P hP := C.placeMap_not_mem_nodes (σ • P) hP
  pointwise P hP hrat f hf hreg := by
    have hrat' : (σ • P).IsRational := (Place.Transport.isRational_smul_iff σ P).mpr hrat
    have hreg' : ∀ w ∈ C.dom, C.placeMap w = C.placeMap (σ • P) → σ f ∈ w.toValuationSubring := by
      intro w hw hpw
      have hw1 : σ • σ⁻¹ • w ∈ C.dom := by rwa [smul_inv_smul]
      have h := hreg (σ⁻¹ • w) hw1 (by show C.placeMap (σ • σ⁻¹ • w) = C.placeMap (σ • P); rw [smul_inv_smul, hpw])
      rwa [Place.Transport.mem_inv_smul_iff] at h
    obtain ⟨hm, h, heq⟩ := C.pointwise (σ • P) hP hrat' (σ f) hf hreg'
    have e := Place.Transport.evalAt_smul σ P hrat f
    refine ⟨hm, e ▸ h, ?_⟩
    have hsub : (⟨P.evalAt f, e ▸ h⟩ : A) = ⟨(σ • P).evalAt (σ f), h⟩ := Subtype.ext e.symm
    rw [hsub]
    exact heq
  mapDomain_placeMap f hf D hD hD0 Q hQ := by
    have hmap : Finsupp.mapDomain (fun P => C.placeMap (σ • P)) D = Finsupp.mapDomain C.placeMap (σ • D) := by
      rw [Divisor.smul_def, ← Finsupp.mapDomain_comp]; rfl
    rw [hmap]
    have key := C.mapDomain_placeMap ⟨σ (f : F), f.2⟩ (by simpa [comapResidue_apply] using hf) (σ • D)
      (fun P hP => by
        rw [Divisor.smul_apply, hD (σ⁻¹ • P) (show σ • σ⁻¹ • P ∈ C.dom by rwa [smul_inv_smul]), Place.Transport.ord_inv_smul])
      (fun P hP => by
        rw [Divisor.smul_apply]
        exact hD0 _ (fun h => hP (by rwa [Set.mem_setOf_eq, smul_inv_smul] at h)))
      Q hQ
    rw [key, comapResidue_apply]

end ComponentChart

namespace Annulus

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  (σ : F ≃ₐ[L] F) (An : Annulus A F)

def comap : Annulus A F where
  dom := {P | σ • P ∈ An.dom}
  param := σ.symm An.param
  modulus := An.modulus
  modulus_mem := An.modulus_mem
  mem_dom P hP := by
    obtain ⟨hrat, hmem, hval, hne, hmod⟩ := An.mem_dom (σ • P) hP
    have hratP : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp hrat
    refine ⟨hratP, (Place.Transport.mem_smul_iff σ P An.param).mp hmem, ?_, ?_, ?_⟩ <;>
      rw [Place.Transport.evalAt_symm σ P hratP]
    exacts [hval, hne, hmod]
  existsUnique_evalAt_eq c hc hc0 hmod := by
    obtain ⟨P₀, ⟨hP₀, hval⟩, huniq⟩ := An.existsUnique_evalAt_eq c hc hc0 hmod
    refine ⟨σ⁻¹ • P₀, ⟨?_, ?_⟩, ?_⟩
    · show σ • σ⁻¹ • P₀ ∈ An.dom; rwa [smul_inv_smul]
    · have hrat : (σ⁻¹ • P₀).IsRational := by
        rw [← Place.Transport.isRational_smul_iff σ, smul_inv_smul]; exact (An.mem_dom _ hP₀).1
      rw [Place.Transport.evalAt_symm σ _ hrat, smul_inv_smul]; exact hval
    · rintro P ⟨hP, hPval⟩
      have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
      rw [Place.Transport.evalAt_symm σ P hrat] at hPval
      have := huniq (σ • P) ⟨hP, hPval⟩
      rw [← this, inv_smul_smul]
  ord_param_sub P hP := by
    have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
    have h := An.ord_param_sub (σ • P) hP
    rw [Place.Transport.ord_smul', map_sub, AlgEquiv.commutes] at h
    rw [Place.Transport.evalAt_symm σ P hrat]
    exact h
  unit_principle f hf0 hord := by
    have hord' : ∀ P₀ ∈ An.dom, P₀.ord (σ f) = 0 := by
      intro P₀ hP₀
      have h := hord (σ⁻¹ • P₀) (show σ • σ⁻¹ • P₀ ∈ An.dom by rwa [smul_inv_smul])
      rwa [Place.Transport.ord_inv_smul] at h
    obtain ⟨m, c, hc, H⟩ := An.unit_principle (σ f) (by simpa using hf0) hord'
    refine ⟨m, c, hc, fun P hP => ?_⟩
    have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
    obtain ⟨h, hu⟩ := H (σ • P) hP
    have key : P.evalAt f * c⁻¹ * P.evalAt (σ.symm An.param) ^ (-m)
        = (σ • P).evalAt (σ f) * c⁻¹ * (σ • P).evalAt An.param ^ (-m) := by
      rw [Place.Transport.evalAt_smul σ P hrat, Place.Transport.evalAt_symm σ P hrat]
    refine ⟨key ▸ h, ?_⟩
    have hsub : (⟨_, key ▸ h⟩ : A) = ⟨_, h⟩ := Subtype.ext key
    rw [hsub]; exact hu

variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

end Annulus

namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (σ τ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)

end ComponentChart

end AlgebraicCurve

end
