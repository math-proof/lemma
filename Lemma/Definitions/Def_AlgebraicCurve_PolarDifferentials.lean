import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_RegularDifferentials
import Lemma.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

def IsRegularAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord

def HasSimplePoleAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f : F, v.uniformizer * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord

def HasSimpleResidue (ω : Ω[F⁄K]) (a : K) : Prop :=
  ∃ f : F, ω = f • v.dCoord ∧ v.HasValue (v.uniformizer * f) a

variable {v}

variable (v) in

theorem uniformizer_mem_toValuationSubring : v.uniformizer ∈ v.toValuationSubring :=
  SetLike.coe_mem (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

variable (v) in

theorem irreducible_mk_uniformizer :
    Irreducible (⟨v.uniformizer, v.uniformizer_mem_toValuationSubring⟩ : v.toValuationSubring) := by
  have h := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  exact h

theorem IsRegularAt.hasSimplePoleAt {ω : Ω[F⁄K]} (h : v.IsRegularAt ω) : v.HasSimplePoleAt ω := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨f, mul_mem v.uniformizer_mem_toValuationSubring hf, rfl⟩

theorem HasSimpleResidue.hasSimplePoleAt {ω : Ω[F⁄K]} {a : K} (h : v.HasSimpleResidue ω a) :
    v.HasSimplePoleAt ω := by
  obtain ⟨f, rfl, hval⟩ := h
  exact ⟨f, hval.mem, rfl⟩

variable (v) in
theorem isRegularAt_zero : v.IsRegularAt (0 : Ω[F⁄K]) :=
  ⟨0, zero_mem _, by rw [zero_smul]⟩

theorem IsRegularAt.add {ω η : Ω[F⁄K]} (hω : v.IsRegularAt ω) (hη : v.IsRegularAt η) :
    v.IsRegularAt (ω + η) := by
  obtain ⟨f, hf, rfl⟩ := hω
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨f + g, add_mem hf hg, by rw [add_smul]⟩

theorem IsRegularAt.smul (c : K) {ω : Ω[F⁄K]} (hω : v.IsRegularAt ω) : v.IsRegularAt (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨algebraMap K F c * f, mul_mem (v.algebraMap_mem' c) hf, ?_⟩
  rw [mul_smul, algebraMap_smul]

variable (v) in
theorem hasSimplePoleAt_zero : v.HasSimplePoleAt (0 : Ω[F⁄K]) :=
  ⟨0, by rw [mul_zero]; exact zero_mem _, by rw [zero_smul]⟩

theorem HasSimplePoleAt.add {ω η : Ω[F⁄K]} (hω : v.HasSimplePoleAt ω) (hη : v.HasSimplePoleAt η) :
    v.HasSimplePoleAt (ω + η) := by
  obtain ⟨f, hf, rfl⟩ := hω
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨f + g, by rw [mul_add]; exact add_mem hf hg, by rw [add_smul]⟩

theorem HasSimplePoleAt.smul (c : K) {ω : Ω[F⁄K]} (hω : v.HasSimplePoleAt ω) :
    v.HasSimplePoleAt (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨algebraMap K F c * f, ?_, by rw [mul_smul, algebraMap_smul]⟩
  rw [mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hf

theorem hasSimpleResidue_zero_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasSimpleResidue (f • v.dCoord) 0 := by
  refine ⟨f, rfl, mul_mem v.uniformizer_mem_toValuationSubring hf, ?_⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff]
  have hx : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem_toValuationSubring hf⟩ : v.toValuationSubring) =
      ⟨v.uniformizer, v.uniformizer_mem_toValuationSubring⟩ * ⟨f, hf⟩ := rfl
  rw [hx]
  exact Ideal.mul_mem_right _ _
    ((IsLocalRing.mem_maximalIdeal _).mpr v.irreducible_mk_uniformizer.not_isUnit)

end Place

section Polar

variable (K F)

def polarDifferentials (S : Set (Place K F)) : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, (v ∉ S → v.IsRegularAt ω) ∧ (v ∈ S → v.HasSimplePoleAt ω)}
  zero_mem' v := ⟨fun _ => v.isRegularAt_zero, fun _ => v.hasSimplePoleAt_zero⟩
  add_mem' hω hη v :=
    ⟨fun hv => ((hω v).1 hv).add ((hη v).1 hv), fun hv => ((hω v).2 hv).add ((hη v).2 hv)⟩
  smul_mem' c _ hω v := ⟨fun hv => ((hω v).1 hv).smul c, fun hv => ((hω v).2 hv).smul c⟩

variable {K F}

theorem mem_polarDifferentials_iff {S : Set (Place K F)} {ω : Ω[F⁄K]} :
    ω ∈ polarDifferentials K F S ↔
      ∀ v : Place K F, (v ∉ S → v.IsRegularAt ω) ∧ (v ∈ S → v.HasSimplePoleAt ω) :=
  Iff.rfl

theorem hasSimplePoleAt_of_mem_polarDifferentials {S : Set (Place K F)} {ω : Ω[F⁄K]}
    (h : ω ∈ polarDifferentials K F S) (v : Place K F) : v.HasSimplePoleAt ω := by
  by_cases hv : v ∈ S
  · exact (h v).2 hv
  · exact ((h v).1 hv).hasSimplePoleAt

theorem regularDifferentials_le_polarDifferentials (S : Set (Place K F)) :
    regularDifferentials K F ≤ polarDifferentials K F S := fun ω hω v =>
  ⟨fun _ => hω v, fun _ => (show v.IsRegularAt ω from hω v).hasSimplePoleAt⟩

theorem polarDifferentials_mono {S T : Set (Place K F)} (h : S ⊆ T) :
    polarDifferentials K F S ≤ polarDifferentials K F T := fun _ hω v =>
  ⟨fun hv => (hω v).1 fun hs => hv (h hs), fun _ => hasSimplePoleAt_of_mem_polarDifferentials hω v⟩

theorem polarDifferentials_empty : polarDifferentials K F ∅ = regularDifferentials K F := by
  refine le_antisymm (fun ω hω v => (hω v).1 (Set.notMem_empty v)) ?_
  exact regularDifferentials_le_polarDifferentials ∅

end Polar

section Glued

variable (K F)

def IsGluedPolarPair (S : Set (Place K F × Place K F)) (ω : Ω[F⁄K] × Ω[F⁄K]) : Prop :=
  ω.1 ∈ polarDifferentials K F (Prod.fst '' S) ∧ ω.2 ∈ polarDifferentials K F (Prod.snd '' S) ∧
    ∀ s ∈ S, ∀ a b : K, s.1.HasSimpleResidue ω.1 a → s.2.HasSimpleResidue ω.2 b → a + b = 0

def gluedPolarDifferentials (S : Set (Place K F × Place K F)) : Submodule K (Ω[F⁄K] × Ω[F⁄K]) :=
  Submodule.span K {ω | IsGluedPolarPair K F S ω}

variable {K F}

theorem mem_gluedPolarDifferentials_of_isGluedPolarPair {S : Set (Place K F × Place K F)}
    {ω : Ω[F⁄K] × Ω[F⁄K]} (h : IsGluedPolarPair K F S ω) : ω ∈ gluedPolarDifferentials K F S :=
  Submodule.subset_span h

theorem gluedPolarDifferentials_eq_span (S : Set (Place K F × Place K F)) :
    gluedPolarDifferentials K F S = Submodule.span K {ω | IsGluedPolarPair K F S ω} :=
  rfl

theorem gluedPolarDifferentials_le_prod (S : Set (Place K F × Place K F)) :
    gluedPolarDifferentials K F S ≤
      (polarDifferentials K F (Prod.fst '' S)).prod (polarDifferentials K F (Prod.snd '' S)) := by
  rw [gluedPolarDifferentials, Submodule.span_le]
  rintro ω ⟨h1, h2, -⟩
  exact ⟨h1, h2⟩

variable (K F) in

def gluedPolarDifferentials.fst (S : Set (Place K F × Place K F)) :
    gluedPolarDifferentials K F S →ₗ[K] polarDifferentials K F (Prod.fst '' S) :=
  ((LinearMap.fst K Ω[F⁄K] Ω[F⁄K]).domRestrict _).codRestrict _ fun ω =>
    (gluedPolarDifferentials_le_prod S ω.2).1

variable (K F) in

def gluedPolarDifferentials.snd (S : Set (Place K F × Place K F)) :
    gluedPolarDifferentials K F S →ₗ[K] polarDifferentials K F (Prod.snd '' S) :=
  ((LinearMap.snd K Ω[F⁄K] Ω[F⁄K]).domRestrict _).codRestrict _ fun ω =>
    (gluedPolarDifferentials_le_prod S ω.2).2

@[simp]
theorem gluedPolarDifferentials.coe_fst_apply (S : Set (Place K F × Place K F))
    (ω : gluedPolarDifferentials K F S) :
    (gluedPolarDifferentials.fst K F S ω : Ω[F⁄K]) = (ω : Ω[F⁄K] × Ω[F⁄K]).1 :=
  rfl

@[simp]
theorem gluedPolarDifferentials.coe_snd_apply (S : Set (Place K F × Place K F))
    (ω : gluedPolarDifferentials K F S) :
    (gluedPolarDifferentials.snd K F S ω : Ω[F⁄K]) = (ω : Ω[F⁄K] × Ω[F⁄K]).2 :=
  rfl

theorem prod_regularDifferentials_le_gluedPolarDifferentials_empty :
    (regularDifferentials K F).prod (regularDifferentials K F) ≤
      gluedPolarDifferentials K F (∅ : Set (Place K F × Place K F)) := by
  rintro ω ⟨h1, h2⟩
  refine mem_gluedPolarDifferentials_of_isGluedPolarPair ⟨?_, ?_, fun s hs => (Set.notMem_empty s hs).elim⟩
  · rw [Set.image_empty, polarDifferentials_empty]; exact h1
  · rw [Set.image_empty, polarDifferentials_empty]; exact h2

end Glued

end AlgebraicCurve

end
