import Mathlib
import Lemma.AlgebraicCurve.CechSectionsOfDivisor
import Lemma.AlgebraicCurve.Correspondence

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem preimage_restrictAlong_union_eq_univ (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) :
    (Place.restrictAlong φ hφ) ⁻¹' S₀ ∪ (Place.restrictAlong φ hφ) ⁻¹' S₁ = Set.univ := by
  rw [← Set.preimage_union, hcover, Set.preimage_univ]

theorem map_mem_lSpaceOn_preimage (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {S : Set (Place K F)} {f : F} (hf : f ∈ lSpaceOn S (0 : Divisor K F)) :
    φ f ∈ lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S) (0 : Divisor K F') := by
  rw [mem_lSpaceOn_iff_ord] at hf ⊢
  intro w hw
  rcases hf (w.restrictAlong φ hφ) hw with h | h
  · exact Or.inl (by rw [h, map_zero])
  · refine Or.inr ?_
    rw [Finsupp.coe_zero, Pi.zero_apply, neg_zero] at h ⊢
    rw [Place.ord_restrictAlong φ hφ w f]
    exact mul_nonneg (Int.natCast_nonneg _) h

def lSpaceOnZero.pullbackAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (S₀ S₁ : Set (Place K F)) :
    ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)) →ₗ[K]
      ↥(lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S₀ ∩ (Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F')) :=
  LinearMap.codRestrict _ (φ.toLinearMap.comp (lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)).subtype)
    (fun f => map_mem_lSpaceOn_preimage φ hφ f.2)

@[simp] theorem lSpaceOnZero.coe_pullbackAlong_apply (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (S₀ S₁ : Set (Place K F)) (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) :
    (lSpaceOnZero.pullbackAlong φ hφ S₀ S₁ f : F') = φ (f : F) := rfl

theorem range_cechDiff_le_comap_pullbackAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (S₀ S₁ : Set (Place K F)) :
    LinearMap.range (cechDiff S₀ S₁ (0 : Divisor K F))
      ≤ (LinearMap.range (cechDiff ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁)
          (0 : Divisor K F'))).comap (lSpaceOnZero.pullbackAlong φ hφ S₀ S₁) := by
  intro g hg
  rw [Submodule.mem_comap, mem_range_cechDiff_iff, lSpaceOnZero.coe_pullbackAlong_apply]
  rw [mem_range_cechDiff_iff] at hg
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hg
  rw [← hab, map_add]
  exact Submodule.add_mem_sup (map_mem_lSpaceOn_preimage φ hφ ha) (map_mem_lSpaceOn_preimage φ hφ hb)

def cechH1.pullbackAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (S₀ S₁ : Set (Place K F)) :
    cechH1 S₀ S₁ (0 : Divisor K F) →ₗ[K]
      cechH1 ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F') :=
  Submodule.mapQ _ _ (lSpaceOnZero.pullbackAlong φ hφ S₀ S₁)
    (range_cechDiff_le_comap_pullbackAlong φ hφ S₀ S₁)

@[simp] theorem cechH1.pullbackAlong_mk (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (S₀ S₁ : Set (Place K F)) (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) :
    cechH1.pullbackAlong φ hφ S₀ S₁ (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (lSpaceOnZero.pullbackAlong φ hφ S₀ S₁ f) := rfl

def traceFunAlong (φ : F →ₐ[K] F') : F' →ₗ[K] F :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  (Algebra.trace F F').restrictScalars K

theorem traceFunAlong_apply (φ : F →ₐ[K] F') (f' : F') :
    traceFunAlong φ f' = (letI := algebraAlong φ; Algebra.trace F F' f') := rfl

def TraceIntegralAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : Prop :=
  ∀ (v : Place K F) (f' : F'),
    (∀ w : Place K F', w.restrictAlong φ hφ = v → f' ∈ w.toValuationSubring) →
      traceFunAlong φ f' ∈ v.toValuationSubring

namespace Place

theorem zero_le_ord_of_mem_toValuationSubring (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [v.ord_zero]
  · exact ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem mem_toValuationSubring_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem mem_lSpaceOn_zero_iff_forall_mem {S : Set (Place K F)} {f : F} :
    f ∈ lSpaceOn S (0 : Divisor K F) ↔ ∀ v ∈ S, f ∈ v.toValuationSubring := by
  rw [mem_lSpaceOn_iff_ord]
  refine forall₂_congr fun v _ => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
  constructor
  · rintro (rfl | h)
    · exact zero_mem _
    · exact v.mem_toValuationSubring_of_ord_nonneg h
  · exact fun h => Or.inr (v.zero_le_ord_of_mem_toValuationSubring h)

end Place

theorem traceFunAlong_mem_lSpaceOn {φ : F →ₐ[K] F'} {hφ : φ.toRingHom.IsIntegral}
    (htr : TraceIntegralAlong φ hφ) {S : Set (Place K F)} {f' : F'}
    (hf' : f' ∈ lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S) (0 : Divisor K F')) :
    traceFunAlong φ f' ∈ lSpaceOn S (0 : Divisor K F) := by
  rw [Place.mem_lSpaceOn_zero_iff_forall_mem] at hf' ⊢
  intro v hv
  refine htr v f' fun w hw => hf' w ?_
  rw [Set.mem_preimage, hw]
  exact hv

def lSpaceOnZero.traceAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (htr : TraceIntegralAlong φ hφ) (S₀ S₁ : Set (Place K F)) :
    ↥(lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S₀ ∩ (Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F'))
      →ₗ[K] ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)) :=
  LinearMap.codRestrict _ ((traceFunAlong φ).comp (lSpaceOn _ (0 : Divisor K F')).subtype)
    (fun f' => traceFunAlong_mem_lSpaceOn htr (S := S₀ ∩ S₁)
      (by rw [Set.preimage_inter]; exact f'.2))

@[simp] theorem lSpaceOnZero.coe_traceAlong_apply (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (htr : TraceIntegralAlong φ hφ) (S₀ S₁ : Set (Place K F))
    (f' : ↥(lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S₀ ∩ (Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F'))) :
    (lSpaceOnZero.traceAlong φ hφ htr S₀ S₁ f' : F) = traceFunAlong φ (f' : F') := rfl

theorem range_cechDiff_le_comap_traceAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (htr : TraceIntegralAlong φ hφ) (S₀ S₁ : Set (Place K F)) :
    LinearMap.range (cechDiff ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁)
        (0 : Divisor K F'))
      ≤ (LinearMap.range (cechDiff S₀ S₁ (0 : Divisor K F))).comap (lSpaceOnZero.traceAlong φ hφ htr S₀ S₁) := by
  intro g hg
  rw [Submodule.mem_comap, mem_range_cechDiff_iff, lSpaceOnZero.coe_traceAlong_apply]
  rw [mem_range_cechDiff_iff] at hg
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hg
  rw [← hab, map_add]
  exact Submodule.add_mem_sup (traceFunAlong_mem_lSpaceOn htr ha) (traceFunAlong_mem_lSpaceOn htr hb)

def cechH1.traceAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (htr : TraceIntegralAlong φ hφ)
    (S₀ S₁ : Set (Place K F)) :
    cechH1 ((Place.restrictAlong φ hφ) ⁻¹' S₀) ((Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F')
      →ₗ[K] cechH1 S₀ S₁ (0 : Divisor K F) :=
  Submodule.mapQ _ _ (lSpaceOnZero.traceAlong φ hφ htr S₀ S₁)
    (range_cechDiff_le_comap_traceAlong φ hφ htr S₀ S₁)

@[simp] theorem cechH1.traceAlong_mk (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (htr : TraceIntegralAlong φ hφ) (S₀ S₁ : Set (Place K F))
    (f' : ↥(lSpaceOn ((Place.restrictAlong φ hφ) ⁻¹' S₀ ∩ (Place.restrictAlong φ hφ) ⁻¹' S₁) (0 : Divisor K F'))) :
    cechH1.traceAlong φ hφ htr S₀ S₁ (Submodule.Quotient.mk f')
      = Submodule.Quotient.mk (lSpaceOnZero.traceAlong φ hφ htr S₀ S₁ f') := rfl

end AlgebraicCurve

end
