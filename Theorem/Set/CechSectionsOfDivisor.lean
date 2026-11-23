module

public import Theorem.Submodule.Repartitions
public import Theorem.LinearMap.TwoChartCech

public noncomputable section

set_option autoImplicit false

noncomputable section

open WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


public theorem mem_lSpaceOn_iff {S : Set (Place K F)} {D : Divisor K F} {f : F} :
    f ∈ lSpaceOn S D ↔ ∀ v ∈ S, v.adicValuation f ≤ exp (D v) := Iff.rfl


public theorem mem_lSpaceOn_iff_ord {S : Set (Place K F)} {D : Divisor K F} {f : F} :
    f ∈ lSpaceOn S D ↔ ∀ v ∈ S, f = 0 ∨ -D v ≤ v.ord f :=
  forall₂_congr fun v _ => v.adicValuation_le_exp_iff


@[simp] public theorem lSpaceOn_univ (D : Divisor K F) :
    lSpaceOn (Set.univ : Set (Place K F)) D = riemannRochSpace D := by
  ext f
  exact ⟨fun h v => h v (Set.mem_univ v), fun h v _ => h v⟩


@[simp] public theorem lSpaceOn_empty (D : Divisor K F) :
    lSpaceOn (∅ : Set (Place K F)) D = ⊤ := by
  ext f
  simp [mem_lSpaceOn_iff]


public theorem lSpaceOn_anti {S₀ S₁ : Set (Place K F)} (h : S₀ ⊆ S₁) (D : Divisor K F) :
    lSpaceOn S₁ D ≤ lSpaceOn S₀ D := fun _ hf v hv => hf v (h hv)


public theorem riemannRochSpace_le_lSpaceOn (S : Set (Place K F)) (D : Divisor K F) :
    riemannRochSpace D ≤ lSpaceOn S D := fun _ hf v _ => hf v


public theorem lSpaceOn_mono {D E : Divisor K F} (hDE : D ≤ E) (S : Set (Place K F)) :
    lSpaceOn S D ≤ lSpaceOn S E := fun _ hf v hv =>
  (hf v hv).trans (exp_le_exp.mpr (hDE v))


public theorem lSpaceOn_union (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    lSpaceOn (S₀ ∪ S₁) D = lSpaceOn S₀ D ⊓ lSpaceOn S₁ D := by
  ext f
  simp only [mem_lSpaceOn_iff, Submodule.mem_inf, Set.mem_union]
  exact ⟨fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩,
    fun ⟨h₀, h₁⟩ v hv => hv.elim (h₀ v) (h₁ v)⟩


public theorem lSpaceOn_inf_eq_of_cover {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (D : Divisor K F) :
    lSpaceOn S₀ D ⊓ lSpaceOn S₁ D = riemannRochSpace D := by
  rw [← lSpaceOn_union, hcover, lSpaceOn_univ]


public theorem lSpaceOn_eq_iInf_singleton (S : Set (Place K F)) (D : Divisor K F) :
    lSpaceOn S D = ⨅ v ∈ S, lSpaceOn {v} D := by
  ext f
  simp only [mem_lSpaceOn_iff, Submodule.mem_iInf, Set.mem_singleton_iff, forall_eq]


public theorem mem_lSpaceOn_singleton_iff {v : Place K F} {D : Divisor K F} {f : F} :
    f ∈ lSpaceOn {v} D ↔ f = 0 ∨ -D v ≤ v.ord f := by
  rw [mem_lSpaceOn_iff_ord]
  simp


public theorem coe_cechDiff_apply {S₀ S₁ : Set (Place K F)} {D : Divisor K F}
    (p : lSpaceOn S₀ D × lSpaceOn S₁ D) :
    (cechDiff S₀ S₁ D p : F) = (p.2 : F) - p.1 := by
  have h := congrArg (fun x : lSpaceOn (S₀ ∩ S₁) D => (x : F))
    (TwoChartCech.Sections.cechDiff_apply (cechSections S₀ S₁ D) p)
  refine h.trans ?_
  rfl


public theorem cechH0_eq (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    cechH0 S₀ S₁ D = (cechSections S₀ S₁ D).H0 := rfl


public theorem mem_cechH0_iff {S₀ S₁ : Set (Place K F)} {D : Divisor K F}
    (p : lSpaceOn S₀ D × lSpaceOn S₁ D) :
    p ∈ cechH0 S₀ S₁ D ↔ (p.1 : F) = p.2 :=
  TwoChartCech.Sections.mem_H0_ofSubmodules_iff _ _ _ _ _ p


public theorem cechH1_eq (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    cechH1 S₀ S₁ D = (cechSections S₀ S₁ D).H1 := rfl


public theorem map_subtype_range_cechDiff (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    (LinearMap.range (cechDiff S₀ S₁ D)).map (lSpaceOn (S₀ ∩ S₁) D).subtype
      = lSpaceOn S₀ D ⊔ lSpaceOn S₁ D := by
  apply le_antisymm
  · rintro _ ⟨y, ⟨p, rfl⟩, rfl⟩
    rw [Submodule.coe_subtype, coe_cechDiff_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right p.2.2) (Submodule.mem_sup_left p.1.2)
  · refine sup_le ?_ ?_
    · intro f hf
      refine ⟨⟨f, lSpaceOn_anti Set.inter_subset_left D hf⟩,
        ⟨((-⟨f, hf⟩ : lSpaceOn S₀ D), 0), ?_⟩, rfl⟩
      apply Subtype.ext
      rw [coe_cechDiff_apply]
      simp
    · intro f hf
      refine ⟨⟨f, lSpaceOn_anti Set.inter_subset_right D hf⟩, ⟨(0, ⟨f, hf⟩), ?_⟩, rfl⟩
      apply Subtype.ext
      rw [coe_cechDiff_apply]
      simp


public theorem mem_range_cechDiff_iff {S₀ S₁ : Set (Place K F)} {D : Divisor K F}
    (g : lSpaceOn (S₀ ∩ S₁) D) :
    g ∈ LinearMap.range (cechDiff S₀ S₁ D) ↔ (g : F) ∈ lSpaceOn S₀ D ⊔ lSpaceOn S₁ D := by
  rw [← map_subtype_range_cechDiff, Submodule.mem_map]
  constructor
  · exact fun h => ⟨g, h, rfl⟩
  · rintro ⟨g', hg', hgg'⟩
    rwa [← Subtype.ext hgg']


@[simp] public theorem coe_cechH0Equiv_apply {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (D : Divisor K F) (p : cechH0 S₀ S₁ D) :
    (cechH0Equiv hcover D p : F) = ((p.1.1 : lSpaceOn S₀ D) : F) := rfl

section ToH1

variable (K) in
open Classical in


public theorem coe_offChartIndicator_apply (S : Set (Place K F)) (v : Place K F) :
    (offChartIndicator K S : Place K F → F) v = if v ∈ S then 0 else 1 := rfl

variable (K) in


public theorem coe_extendOffChart_apply (S₀ : Set (Place K F)) (f : F) (v : Place K F) :
    (extendOffChart K S₀ f : Place K F → F) v = if v ∈ S₀ then 0 else f := by
  show ((offChartIndicator K S₀ : Place K F → F) * algebraMap F (Place K F → F) f) v = _
  rw [Pi.mul_apply, coe_offChartIndicator_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs <;> simp


public theorem coe_extendOffChart_apply_of_mem {S₀ : Set (Place K F)} (f : F) {v : Place K F}
    (hv : v ∈ S₀) : (extendOffChart K S₀ f : Place K F → F) v = 0 := by
  classical
  rw [coe_extendOffChart_apply, if_pos hv]


public theorem coe_extendOffChart_apply_of_not_mem {S₀ : Set (Place K F)} (f : F) {v : Place K F}
    (hv : v ∉ S₀) : (extendOffChart K S₀ f : Place K F → F) v = f := by
  classical
  rw [coe_extendOffChart_apply, if_neg hv]


public theorem algebraMap_sub_extendOffChart_mem_repartitionsOf {S₀ : Set (Place K F)} {D : Divisor K F}
    {f : F} (hf : f ∈ lSpaceOn S₀ D) :
    algebraMap F (↥(repartitions K F)) f - extendOffChart K S₀ f ∈ repartitionsOf D := by
  intro v
  rw [AddSubgroupClass.coe_sub, Pi.sub_apply, Subalgebra.coe_algebraMap, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hv : v ∈ S₀
  · rw [coe_extendOffChart_apply_of_mem f hv, sub_zero]
    exact hf v hv
  · rw [coe_extendOffChart_apply_of_not_mem f hv, sub_self]
    simp


public theorem extendOffChart_mem_repartitionsOf {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    {D : Divisor K F} {f : F} (hf : f ∈ lSpaceOn S₁ D) :
    extendOffChart K S₀ f ∈ repartitionsOf D := by
  intro v
  by_cases hv : v ∈ S₀
  · rw [coe_extendOffChart_apply_of_mem f hv]
    simp
  · rw [coe_extendOffChart_apply_of_not_mem f hv]
    have hv₁ : v ∈ S₁ := by
      have : v ∈ S₀ ∪ S₁ := hcover ▸ Set.mem_univ v
      exact this.resolve_left hv
    exact hf v hv₁


public theorem algebraMap_mem_principalRepartitions (f : F) :
    algebraMap F (↥(repartitions K F)) f ∈ principalRepartitions K F :=
  mem_principalRepartitions_iff.mpr ⟨f, rfl⟩


public theorem toH1Aux_apply {S₀ S₁ : Set (Place K F)} {D : Divisor K F} (f : lSpaceOn (S₀ ∩ S₁) D) :
    toH1Aux S₀ S₁ D f = Submodule.Quotient.mk (extendOffChart K S₀ (f : F)) := rfl


public theorem range_cechDiff_le_ker_toH1Aux {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (D : Divisor K F) :
    LinearMap.range (cechDiff S₀ S₁ D) ≤ LinearMap.ker (toH1Aux S₀ S₁ D) := by
  rintro g ⟨p, rfl⟩
  rw [LinearMap.mem_ker, toH1Aux_apply, Submodule.Quotient.mk_eq_zero, coe_cechDiff_apply,
    map_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · exact Submodule.mem_sup_left (extendOffChart_mem_repartitionsOf hcover p.2.2)
  · rw [show extendOffChart K S₀ (p.1 : F) = algebraMap F (↥(repartitions K F)) (p.1 : F)
        - (algebraMap F (↥(repartitions K F)) (p.1 : F) - extendOffChart K S₀ (p.1 : F)) by abel]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (algebraMap_mem_principalRepartitions _))
      (Submodule.mem_sup_left (algebraMap_sub_extendOffChart_mem_repartitionsOf p.1.2))


@[simp] public theorem cechH1ToH1_mk {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (D : Divisor K F) (f : lSpaceOn (S₀ ∩ S₁) D) :
    cechH1ToH1 hcover D (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (extendOffChart K S₀ (f : F)) := rfl

end ToH1

end AlgebraicCurve

end
