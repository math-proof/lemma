import Mathlib
import Lemma.Definitions.Def_GroupCohomology_TateCohomology

set_option autoImplicit false

universe u v w

open CategoryTheory

noncomputable section

namespace Rep

section SeamLow

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {X : ShortComplex (Rep.{w} k G)}

lemma seam_range_eq_ker (hX : X.ShortExact) :
    LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
  (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker

lemma seam_f_injective (hX : X.ShortExact) : Function.Injective X.f.hom :=
  (Rep.mono_iff_injective X.f).1 hX.mono_f

lemma seam_g_surjective (hX : X.ShortExact) : Function.Surjective X.g.hom :=
  (Rep.epi_iff_surjective X.g).1 hX.epi_g

lemma seam_g_f_apply (X : ShortComplex (Rep.{w} k G)) (a : X.X₁) : X.g.hom (X.f.hom a) = 0 := by
  rw [← Rep.comp_apply, X.zero]; rfl

lemma norm_eq_zero_of_mem_coinvariantsKer (A : Rep.{w} k G) [Fintype G] {x : A}
    (hx : x ∈ Representation.Coinvariants.ker A.ρ) : A.ρ.norm x = 0 := by
  have h : A.ρ.normBar (Representation.Coinvariants.mk A.ρ x) = 0 := by
    rw [show Representation.Coinvariants.mk A.ρ x = 0 from (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
  exact congrArg Subtype.val h

lemma coinvariantsKer_le_map (hX : X.ShortExact) :
    Representation.Coinvariants.ker X.X₃.ρ ≤ (Representation.Coinvariants.ker X.X₂.ρ).map X.g.hom.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨h, c⟩, rfl⟩
  obtain ⟨b, rfl⟩ := seam_g_surjective hX c
  exact ⟨X.X₂.ρ h b - b, Representation.Coinvariants.sub_mem_ker h b, by simp [Rep.hom_comm_apply]⟩

variable [Fintype G]

def seamT (X : ShortComplex (Rep.{w} k G)) : Submodule k X.X₂ :=
  (LinearMap.ker X.X₃.ρ.norm).comap X.g.hom.toLinearMap

lemma mem_seamT_iff (X : ShortComplex (Rep.{w} k G)) (b : X.X₂) : b ∈ seamT X ↔ X.X₃.ρ.norm (X.g.hom b) = 0 := Iff.rfl

lemma norm_mem_range_of_mem_seamT (hX : X.ShortExact) {b : X.X₂} (hb : b ∈ seamT X) :
    X.X₂.ρ.norm b ∈ LinearMap.range X.f.hom.toLinearMap := by
  rw [seam_range_eq_ker hX, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply, Rep.hom_norm_apply]
  exact hb

def seamψ (hX : X.ShortExact) : seamT X →ₗ[k] X.X₁ :=
  (LinearEquiv.ofInjective X.f.hom.toLinearMap (seam_f_injective hX)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (X.X₂.ρ.norm ∘ₗ (seamT X).subtype) (fun b => norm_mem_range_of_mem_seamT hX b.2)

lemma f_seamψ (hX : X.ShortExact) (b : seamT X) : X.f.hom (seamψ hX b) = X.X₂.ρ.norm b :=
  congrArg Subtype.val ((LinearEquiv.ofInjective X.f.hom.toLinearMap (seam_f_injective hX)).apply_symm_apply
    ⟨X.X₂.ρ.norm b, norm_mem_range_of_mem_seamT hX b.2⟩)

lemma seamψ_mem_invariants (hX : X.ShortExact) (b : seamT X) : seamψ hX b ∈ X.X₁.ρ.invariants := by
  rw [Representation.mem_invariants]
  intro h
  apply seam_f_injective hX
  rw [Rep.hom_comm_apply, f_seamψ]
  exact (Representation.mem_invariants _ _).1 (Representation.norm_apply_mem_invariants _ _) h

def seamψbar (hX : X.ShortExact) : seamT X →ₗ[k] X.X₁.tateH0 :=
  (LinearMap.range X.X₁.ρ.normBar).mkQ ∘ₗ LinearMap.codRestrict _ (seamψ hX) (seamψ_mem_invariants hX)

def seamθ (X : ShortComplex (Rep.{w} k G)) : seamT X →ₗ[k] X.X₃.tateHneg1 :=
  LinearMap.codRestrict _ (Representation.Coinvariants.mk X.X₃.ρ ∘ₗ X.g.hom.toLinearMap ∘ₗ (seamT X).subtype) (fun b =>
    LinearMap.mem_ker.2 (Subtype.ext b.2))

lemma coe_seamθ_apply (X : ShortComplex (Rep.{w} k G)) (b : seamT X) :
    (seamθ X b : X.X₃.ρ.Coinvariants) = Representation.Coinvariants.mk X.X₃.ρ (X.g.hom b) := rfl

lemma seamθ_surjective (hX : X.ShortExact) : Function.Surjective (seamθ X) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := seam_g_surjective hX c
  exact ⟨⟨b, congrArg Subtype.val (LinearMap.mem_ker.1 hx)⟩, rfl⟩

lemma ker_seamθ_le (hX : X.ShortExact) : LinearMap.ker (seamθ X) ≤ LinearMap.ker (seamψbar hX) := by
  intro b hb
  rw [LinearMap.mem_ker, Subtype.ext_iff, coe_seamθ_apply] at hb

  obtain ⟨i, hi, hgi⟩ := coinvariantsKer_le_map hX ((Submodule.Quotient.mk_eq_zero _).1 hb)
  have hbi : (b : X.X₂) - i ∈ LinearMap.range X.f.hom.toLinearMap := by
    rw [seam_range_eq_ker hX, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hgi.symm
  obtain ⟨a₀, ha₀⟩ := hbi

  rw [LinearMap.mem_ker, seamψbar, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨Representation.Coinvariants.mk _ a₀, Subtype.ext (seam_f_injective hX ?_)⟩
  rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, LinearMap.codRestrict_apply, f_seamψ,
    Rep.hom_norm_apply]
  change X.X₂.ρ.norm (X.f.hom.toLinearMap a₀) = _
  rw [ha₀, map_sub, norm_eq_zero_of_mem_coinvariantsKer _ hi, sub_zero]

def tateδneg1 (hX : X.ShortExact) : X.X₃.tateHneg1 →ₗ[k] X.X₁.tateH0 :=
  (LinearMap.ker (seamθ X)).liftQ (seamψbar hX) (ker_seamθ_le hX) ∘ₗ
    ((seamθ X).quotKerEquivOfSurjective (seamθ_surjective hX)).symm.toLinearMap

lemma tateδneg1_mk (hX : X.ShortExact) (b : X.X₂) (hb : X.X₃.ρ.norm (X.g.hom b) = 0) (a : X.X₁.ρ.invariants)
    (hab : X.f.hom a = X.X₂.ρ.norm b) :
    tateδneg1 hX (seamθ X ⟨b, hb⟩) = Submodule.Quotient.mk a := by
  rw [tateδneg1, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, (LinearEquiv.symm_apply_eq _).2
    ((LinearMap.quotKerEquivOfSurjective_apply_mk (seamθ X) (seamθ_surjective hX) ⟨b, hb⟩).symm)]
  rw [Submodule.liftQ_apply, seamψbar, LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1
  exact Subtype.ext (seam_f_injective hX ((f_seamψ hX ⟨b, hb⟩).trans hab.symm))

end SeamLow

section SeamGraded

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}

lemma δ₀_normToInvariants (hX : X.ShortExact) (b : X.X₂) :
    groupCohomology.δ hX 0 1 rfl ((groupCohomology.H0Iso X.X₃).inv (X.X₃.ρ.normToInvariants (X.g.hom b))) = 0 := by
  rw [groupCohomology.δ₀_apply hX _ (X.X₂.ρ.norm b)
    (by rw [Representation.coe_normToInvariants_apply, Rep.hom_norm_apply]) 0 (by
      funext h
      change X.f.hom (0 : X.X₁) = X.X₂.ρ h (X.X₂.ρ.norm b) - X.X₂.ρ.norm b
      rw [map_zero, (Representation.mem_invariants _ _).1 (Representation.norm_apply_mem_invariants _ _) h, sub_self])]
  exact (groupCohomology.H1π_eq_zero_iff _).2 (Submodule.zero_mem _)

lemma range_normBar_le_ker_δ₀ (hX : X.ShortExact) :
    LinearMap.range X.X₃.ρ.normBar ≤
      LinearMap.ker ((groupCohomology.H0Iso X.X₃).inv ≫ groupCohomology.δ hX 0 1 rfl).hom := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨b, rfl⟩ := seam_g_surjective hX c
  exact δ₀_normToInvariants hX b

def tateδ₀ (hX : X.ShortExact) : X.X₃.tateH0 →ₗ[k] groupCohomology X.X₁ 1 :=
  (LinearMap.range X.X₃.ρ.normBar).liftQ
    (((groupCohomology.H0Iso X.X₃).inv ≫ groupCohomology.δ hX 0 1 rfl).hom) (range_normBar_le_ker_δ₀ hX)

lemma tateδ₀_mk (hX : X.ShortExact) (z : X.X₃.ρ.invariants) :
    tateδ₀ hX (Submodule.Quotient.mk z) = groupCohomology.δ hX 0 1 rfl ((groupCohomology.H0Iso X.X₃).inv z) := rfl

omit [Fintype G] in

lemma coinvariantsMap_H0Iso_δ (hX : X.ShortExact) (z : groupHomology X.X₃ 1) :
    Rep.coinvariantsMap X.f ((groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl z)) = 0 := by
  have hzero : groupHomology.map (MonoidHom.id G) X.f 0 (groupHomology.δ hX 1 0 rfl z) = 0 :=
    congrArg (fun φ => φ.hom z) (groupHomology.mapShortComplex₁ hX (show 0 + 1 = 1 from rfl)).zero
  have := groupHomology.map_id_comp_H0Iso_hom_apply X.f (groupHomology.δ hX 1 0 rfl z)
  rw [hzero] at this
  exact this.symm.trans (LinearMap.map_zero _)

lemma normBar_H0Iso_δ (hX : X.ShortExact) (z : groupHomology X.X₃ 1) :
    X.X₁.ρ.normBar ((groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl z)) = 0 := by
  have hf : Function.Injective (Rep.invariantsMap X.f) := fun a a' h =>
    Subtype.ext (seam_f_injective hX (congrArg Subtype.val h))
  apply hf
  rw [map_zero, ← LinearMap.comp_apply, ← Rep.normBar_comp_coinvariantsMap, LinearMap.comp_apply,
    coinvariantsMap_H0Iso_δ hX z, map_zero]

def tateδneg2 (hX : X.ShortExact) : groupHomology X.X₃ 1 →ₗ[k] X.X₁.tateHneg1 :=
  LinearMap.codRestrict _ ((groupHomology.δ hX 1 0 rfl ≫ (groupHomology.H0Iso X.X₁).hom).hom) (fun z => by
    rw [LinearMap.mem_ker]
    exact normBar_H0Iso_δ hX z)

@[simp] lemma coe_tateδneg2_apply (hX : X.ShortExact) (z : groupHomology X.X₃ 1) :
    (tateδneg2 hX z : X.X₁.ρ.Coinvariants) = (groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl z) := rfl

end SeamGraded

end Rep

end
