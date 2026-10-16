import Mathlib
import sympy.Basic
open Polynomial
open scoped TensorProduct IntermediateField


private lemma natDegree_minpoly_eq
  [Field k] [Field F] [Field M] [Algebra k F] [Algebra F M] [Algebra k M] [IsScalarTower k F M]
  {β : M}
-- given
  (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range)
  (hβ : IsSeparable k β) :
-- imply
  (minpoly F β).natDegree = (minpoly k β).natDegree := by
-- proof
  set K₁ : IntermediateField k F := algebraicClosure k F with hK₁
  let _ : IsPurelyInseparable k K₁ := by
    rw [isPurelyInseparable_iff]
    intro x
    refine ⟨Algebra.IsIntegral.isIntegral x, fun hx => ?_⟩
    have hx' : IsSeparable k (x : F) :=
      (isSeparable_map_iff K₁.val Subtype.val_injective).mpr hx
    obtain ⟨c, hc⟩ := hsc _ hx'
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [← hc]
    rfl
  have h1 : (minpoly k β).map (algebraMap k K₁) = minpoly K₁ β :=
    minpoly.map_eq_of_isSeparable_of_isPurelyInseparable K₁ β hβ
  have hβi : IsIntegral k β := hβ.isIntegral
  have hβ1 : IsIntegral K₁ β := hβi.tower_top
  have hPm : (minpoly k β).Monic := minpoly.monic hβi
  have hQm : (minpoly F β).Monic := minpoly.monic hβi.tower_top
  have hdvd : minpoly F β ∣ (minpoly k β).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F β
  have hlift : minpoly F β ∈ lifts (algebraMap K₁ F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F hPm hQm hdvd
    rw [lifts_iff_coeff_lifts] at h1
    obtain ⟨c, hc⟩ := h1 n
    refine ⟨⟨(c : F), c.2⟩, hc⟩
  obtain ⟨Q₁, hQ₁, hdeg, hQ₁m⟩ := lifts_and_natDegree_eq_and_monic hlift hQm
  have haeval : aeval β Q₁ = 0 := by
    rw [← aeval_map_algebraMap F β Q₁, hQ₁]
    apply minpoly.aeval F β
  have hd1 : (minpoly K₁ β).natDegree ≤ Q₁.natDegree :=
    natDegree_le_of_dvd (minpoly.dvd K₁ β haeval) hQ₁m.ne_zero
  have hd2 : (minpoly F β).natDegree ≤ (minpoly K₁ β).natDegree := by
    have := natDegree_le_of_dvd (minpoly.dvd_map_of_isScalarTower K₁ F β)
      ((minpoly.monic hβ1).map _).ne_zero
    rwa [natDegree_map] at this
  have h3 : (minpoly K₁ β).natDegree = (minpoly k β).natDegree := by
    rw [← h1, natDegree_map]
  omega

private lemma hsc_range
  [Field k] [Field F] [Field Ω]
  [Algebra k F] [Algebra k Ω]
  {fa : F →ₐ[k] Ω}
  {y : fa.fieldRange}
-- given
  (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range)
  (hy : IsSeparable k y) :
-- imply
  y ∈ (algebraMap k fa.fieldRange).range := by
-- proof
  have h0 : IsSeparable k (fa.fieldRange.val y) :=
    (isSeparable_map_iff fa.fieldRange.val Subtype.val_injective).mpr hy
  obtain ⟨y, z, rfl⟩ := y
  have hz : IsSeparable k z := (isSeparable_map_iff fa fa.injective).mp h0
  obtain ⟨c, hc⟩ := hsc z hz
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change algebraMap k Ω c = fa z
  rw [← hc, fa.commutes]

private lemma linearDisjoint_adjoin_singleton
  [Field k] [Field F] [Field Ω]
  [Algebra k F] [Algebra k Ω]
  {fa : F →ₐ[k] Ω}
  {x : Ω}
-- given
  (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range)
  (hx : IsSeparable k x) :
-- imply
  fa.fieldRange.toSubalgebra.LinearDisjoint (Algebra.adjoin k {x}) := by
-- proof
  have hxi : IsIntegral k x := hx.isIntegral
  let pb := Algebra.adjoin.powerBasis hxi
  refine Subalgebra.LinearDisjoint.of_basis_right _ _ pb.basis ?_
  have hfam : ((Algebra.adjoin k {x}).val ∘ pb.basis : Fin pb.dim → Ω) =
      fun i : Fin pb.dim => x ^ (i : ℕ) := by
    funext i
    simp only [Function.comp_apply, PowerBasis.coe_basis]
    rw [map_pow]
    congr 1
  rw [hfam]
  have hsc' : ∀ y : ↥(fa.fieldRange), IsSeparable k y → y ∈ (algebraMap k ↥(fa.fieldRange)).range := by
    intro y hy
    apply hsc_range (k := k) (F := F) (Ω := Ω) (fa := fa) (y := y) hsc hy
  have hdim : pb.dim = (minpoly fa.fieldRange x).natDegree := by
    rw [Algebra.adjoin.powerBasis_dim hxi,
      natDegree_minpoly_eq (k := k) (F := fa.fieldRange) (M := Ω) hsc' hx]
  have hli : LinearIndependent fa.fieldRange fun i : Fin (minpoly fa.fieldRange x).natDegree =>
      x ^ (i : ℕ) := linearIndependent_pow (K := fa.fieldRange) x
  rw [← hdim] at hli
  apply hli

private lemma exists_le_adjoin_singleton
  [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [Algebra.IsSeparable k K]
  {fb : K →ₐ[k] Ω}
  {B' : Subalgebra k Ω}
-- given
  (hB' : B' ≤ fb.range)
  [Module.Finite k B'] :
-- imply
  ∃ β : K, B' ≤ Algebra.adjoin k {fb β} := by
-- proof
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := k) (M := B')
  have hpre : ∀ i, ∃ y : K, fb y = (s i : Ω) := fun i => hB' (s i).2
  choose y hy using hpre
  let S : Set K := Set.range y
  let K₀ : IntermediateField k K := IntermediateField.adjoin k S
  let _ : FiniteDimensional k K₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let _ : Algebra.IsSeparable k K₀ := Algebra.isSeparable_tower_bot_of_isSeparable k K₀ K
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k K₀
  refine ⟨(α : K), ?_⟩
  have hK₀ : K₀ = k⟮(α : K)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple k K₀ α, hα, IntermediateField.lift_top]
  have hβint : IsIntegral k (α : K) := Algebra.IsIntegral.isIntegral _
  have hmem : ∀ i, (s i : Ω) ∈ Algebra.adjoin k {fb (α : K)} := by
    intro i
    have hyi : y i ∈ K₀ := IntermediateField.subset_adjoin k S ⟨i, rfl⟩
    rw [hK₀, ← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβint.isAlgebraic] at hyi
    rw [← hy i, ← Set.image_singleton, Algebra.adjoin_image]
    apply Subalgebra.mem_map.mpr ⟨y i, hyi, rfl⟩
  intro t ht
  have ht' : (⟨t, ht⟩ : B') ∈ Submodule.span k (Set.range s) := by
    rw [hs]
    apply Submodule.mem_top
  have himg : t ∈ (Submodule.span k (Set.range s)).map B'.val.toLinearMap :=
    ⟨⟨t, ht⟩, ht', rfl⟩
  rw [Submodule.map_span] at himg
  refine (Submodule.span_le.mpr ?_ : Submodule.span k _ ≤
    Subalgebra.toSubmodule (Algebra.adjoin k {fb (α : K)})) himg
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  apply hmem i

private lemma linearDisjoint_range
  [Field k] [Field F] [Field K] [Field Ω]
  [Algebra k F] [Algebra k K] [Algebra k Ω] [Algebra.IsSeparable k K]
  {fa : F →ₐ[k] Ω}
  {fb : K →ₐ[k] Ω}
-- given
  (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
-- imply
  fa.fieldRange.toSubalgebra.LinearDisjoint fb.range := by
-- proof
  let _ : Algebra.IsIntegral k fb.range := by
    refine ⟨fun x => ?_⟩
    obtain ⟨_, y, rfl⟩ := x
    apply (isIntegral_algHom_iff fb.range.val Subtype.val_injective).mp
    apply ((Algebra.IsIntegral.isIntegral (R := k) y).map fb)
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_right _ _ fun B' hB' _ => ?_
  obtain ⟨β, hβ⟩ := exists_le_adjoin_singleton (fb := fb) (B' := B') hB'
  apply (linearDisjoint_adjoin_singleton (fa := fa) hsc ((Algebra.IsSeparable.isSeparable k β).map fb fb.injective)).of_le_right_of_flat hβ


/--
[Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {F : Type v} [Field F] [Algebra k F]
  {K : Type w} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
-- given
  (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
-- imply
  IsField (F ⊗[k] K) := by
-- proof
  apply IntermediateField.LinearDisjoint.isField_of_forall
  intro Ω _ _ fa fb
  rw [IntermediateField.linearDisjoint_iff]
  have hr : (IsScalarTower.toAlgHom k (↥fb.fieldRange) Ω).range = fb.range := by
    ext x
    constructor
    ·
      rintro ⟨⟨_, z, rfl⟩, rfl⟩
      refine ⟨z, rfl⟩
    ·
      rintro ⟨z, rfl⟩
      refine ⟨⟨fb z, z, rfl⟩, rfl⟩
  rw [hr]
  apply linearDisjoint_range (fa := fa) (fb := fb) hsc


-- created on 2026-10-13
