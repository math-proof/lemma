import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GlobalCFT
open NumberField RayClassField Pointwise KroneckerWeber Ideles GlobalCFT
open Ideles
open NumberField RayClassField GlobalCFT


/--
[ArtinSymbol.isArithFrob](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma ArtinSymbol.isArithFrob
  {K : Type v}
  {L : Type v}
  [Field K]
  [Field L]
  {𝔔 : Ideal (RingOfIntegers L)}
  [𝔔.IsPrime]
  [Finite (RingOfIntegers L ⧸ 𝔔)] :
-- imply
  IsArithFrobAt (RingOfIntegers K) (ArtinSymbol K L 𝔔) 𝔔 :=
-- proof
  IsArithFrobAt.arithFrobAt (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔
namespace GlobalCFT
universe u

namespace GlobalCFT

/--
[lemma_22_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma lemma_22_5
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)}
-- given
  (h_dvd : Modulus.dvd 𝔪₂ 𝔪₁)
  (h_cong : IsCongruenceSubgroup K 𝔪₁ 𝒞₁) :
-- imply
  (∃ 𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂), IsCongruenceSubgroup K 𝔪₂ 𝒞₂ ∧ CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) ↔ (∀ x : FracIdealsCoprime K 𝔪₁, (FracIdealsCoprime.inclusion K 𝔪₂ 𝔪₁ h_dvd) x ∈ RayGroup K 𝔪₂ → x ∈ 𝒞₁) := by
-- proof
  constructor
  ·
    rintro ⟨𝒞₂, h_cong₂, 𝔫, h_dvd₁, h_dvd₂, h_eq⟩
    intro x hx
    obtain ⟨r, hr_ray, hr_cop⟩ := FracIdealsCoprime.exists_ray_mul_coprime K 𝔪₁ 𝔫 h_dvd₁ x
    set y : FracIdealsCoprime K 𝔪₁ := x * r⁻¹ with hy_def
    set y' : FracIdealsCoprime K 𝔫 := ⟨y.val, hr_cop⟩ with hy'_def
    have hy'_eq : FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h_dvd₁ y' = y := by
      simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]; rfl
    have hy'_in₂ : y' ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h_dvd₂) 𝒞₂ := by
      rw [Subgroup.mem_comap]
      have hcomp : FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h_dvd₂ y' =
        FracIdealsCoprime.inclusion K 𝔪₂ 𝔪₁ h_dvd
          (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h_dvd₁ y') := by
        rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔪₁ 𝔫 h_dvd h_dvd₁ h_dvd₂]
      rw [hcomp, hy'_eq, hy_def, map_mul, map_inv]
      exact 𝒞₂.mul_mem (h_cong₂.contains_ray hx)
        (𝒞₂.inv_mem (h_cong₂.contains_ray (RayGroup.inclusion_le K 𝔪₂ 𝔪₁ h_dvd r hr_ray)))
    have hy'_in₁ : y' ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h_dvd₁) 𝒞₁ :=
      h_eq ▸ hy'_in₂
    rw [Subgroup.mem_comap] at hy'_in₁
    rw [hy'_eq] at hy'_in₁
    have : x = y * r := by rw [hy_def]; group
    rw [this]
    exact 𝒞₁.mul_mem hy'_in₁ (h_cong.contains_ray hr_ray)
  ·
    intro h_back
    set incl₂₁ := FracIdealsCoprime.inclusion K 𝔪₂ 𝔪₁ h_dvd
    set 𝒞₂ := Subgroup.map incl₂₁ 𝒞₁ ⊔ RayGroup K 𝔪₂ with h𝒞₂_def
    refine ⟨𝒞₂, ⟨le_sup_right⟩, ?_⟩
    refine ⟨𝔪₁, Modulus.dvd_refl 𝔪₁, h_dvd, ?_⟩
    ext x
    simp only [Subgroup.mem_comap]
    have hincl_id : FracIdealsCoprime.inclusion K 𝔪₁ 𝔪₁ (Modulus.dvd_refl 𝔪₁) x = x := by
      simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]; rfl
    constructor
    ·
      intro hx_in
      rw [hincl_id] at hx_in
      exact (le_sup_left : Subgroup.map incl₂₁ 𝒞₁ ≤ 𝒞₂) (Subgroup.mem_map_of_mem _ hx_in)
    ·
      intro hx_in
      rw [hincl_id]
      rw [h𝒞₂_def] at hx_in
      rw [Subgroup.mem_sup] at hx_in
      obtain ⟨a, ha, b, hb, hab⟩ := hx_in
      obtain ⟨y, hy_in, hy_eq⟩ := Subgroup.mem_map.mp ha
      have hxy_ray : incl₂₁ (x * y⁻¹) ∈ RayGroup K 𝔪₂ := by
        rw [map_mul, map_inv, hy_eq]
        have hab' : incl₂₁ x = a * b := hab.symm
        rwa [hab', mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]
      have hxy_in : x * y⁻¹ ∈ 𝒞₁ := h_back _ hxy_ray
      have : x = (x * y⁻¹) * y := by group
      rw [this]
      exact 𝒞₁.mul_mem hxy_in hy_in

end GlobalCFT

namespace GlobalCFT

/--
[conductorOfRayClassCharacter_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma conductorOfRayClassCharacter_dvd
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassCharacter K 𝔪} :
-- imply
  Modulus.dvd (conductorOfRayClassCharacter K 𝔪 χ) 𝔪 := by
-- proof
  unfold conductorOfRayClassCharacter conductorOfCongruenceSubgroup
  have h := (corollary_22_7 K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ)
    (kernelCongruenceSubgroup_isCong K 𝔪 χ)).choose_spec.1.2
  exact h 𝔪 ⟨kernelCongruenceSubgroup K 𝔪 χ, kernelCongruenceSubgroup_isCong K 𝔪 χ,
    congruenceSubgroupEquiv_refl K 𝔪 _⟩

end GlobalCFT

namespace GlobalCFT

/--
[IsCongruenceSubgroup.finiteIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma IsCongruenceSubgroup.finiteIndex
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  𝒞.FiniteIndex := by
-- proof
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ RayGroup K 𝔪) :=
    inferInstanceAs (Finite (RayClassGroup K 𝔪))
  haveI : (RayGroup K 𝔪).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le h_cong.contains_ray

end GlobalCFT

namespace GlobalCFT

/--
[congruenceSubgroup_index_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma congruenceSubgroup_index_pos
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  0 < 𝒞.index := by
-- proof
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ RayGroup K 𝔪) :=
    inferInstanceAs (Finite (RayClassGroup K 𝔪))
  haveI : (RayGroup K 𝔪).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : 𝒞.FiniteIndex := Subgroup.finiteIndex_of_le h_cong.contains_ray
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

end GlobalCFT

namespace GlobalCFT

/--
[dirichletDensity_coprime_primes_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma dirichletDensity_coprime_primes_eq_one
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
-- given
  (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} = some 1 := by
-- proof
  have h_cofin : (Set.univ \ {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True}).Finite := by
    apply Set.Finite.subset (modulus_support_finite K 𝔪)
    intro 𝔭 h𝔭
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_setOf_eq, true_and] at h𝔭
    simp only [Set.mem_setOf_eq]
    intro h_eq
    exact h𝔭 ⟨h_eq, trivial⟩
  have h_polar := proposition_21_14a_cofinite
    {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} h_cofin
  have h_has_polar := polarDensity_eq_some_iff.mp h_polar
  have h_has_dirichlet := polar_implies_dirichlet h_has_polar
  exact dirichletDensity_eq_some_iff.mpr h_has_dirichlet

end GlobalCFT

namespace GlobalCFT

/--
[summable_rpow_inv_absNorm_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma summable_rpow_inv_absNorm_prime
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {s : ℝ}
-- given
  (hs : 1 < s) :
-- imply
  Summable (fun (𝔭 : S) => ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) :=
-- proof
  partialDedekindZeta_dirichletSeries_summable S s hs
set_option maxHeartbeats 400000 in

end GlobalCFT

namespace GlobalCFT

/--
[ps9_dirichletDensity_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma ps9_dirichletDensity_mono
  [Field K]
  [NumberField K]
  {S T : Set (Prime' K)}
  {ρS ρT : ℚ}
-- given
  (hST : S ⊆ T)
  (hS : HasDirichletDensity K S ρS)
  (hT : HasDirichletDensity K T ρT) :
-- imply
  ρS ≤ ρT := by
-- proof
  suffices h : (ρS : ℝ) ≤ (ρT : ℝ) from mod_cast h
  apply le_of_tendsto_of_tendsto hS hT
  have hIoo : Set.Ioo (1 : ℝ) 2 ∈ nhdsWithin 1 (Set.Ioi 1) :=
    Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hIoo] with s hs
  have hs_gt : 1 < s := hs.1
  have hs_lt : s < 2 := hs.2
  have hlog_pos : 0 < Real.log (1 / (s - 1)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < s - 1)]
    linarith
  apply div_le_div_of_nonneg_right _ hlog_pos.le
  exact Summable.tsum_le_tsum_of_inj (Set.inclusion hST)
    (Set.inclusion_injective hST)
    (fun c _ => by positivity)
    (fun i => le_refl _)
    (summable_rpow_inv_absNorm_prime S s hs_gt)
    (summable_rpow_inv_absNorm_prime T s hs_gt)

end GlobalCFT

namespace GlobalCFT

/--
[dirichletDensity_le_of_PrimeSetLe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma dirichletDensity_le_of_PrimeSetLe
  {K : Type u}
  [Field K]
  [NumberField K]
  {S T : Set (Prime' K)}
  {ρS ρT : ℚ}
-- given
  (hle : PrimeSetLe S T)
  (hS_polar : PolarDensity K S = some ρS)
  (hT_dir : HasDirichletDensity K T ρT) :
-- imply
  ρS ≤ ρT := by
-- proof
  have hST_fin : Set.Finite (S \ T) := hle
  have h_symm : Set.Finite (symmDiff S (S ∩ T)) := by
    have : symmDiff S (S ∩ T) = S \ T := by
      ext x
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_diff]
      tauto
    rwa [this]
  have h_union_eq : (S ∩ T) ∪ (S \ T) = S := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]; tauto
  have h_inter_fin : ((S ∩ T) ∩ (S \ T)).Finite := by
    convert Set.finite_empty
    ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false]; tauto
  have h_sdiff_polar : PolarDensity K (S \ T) = some 0 :=
    proposition_21_14a_finite _ hST_fin
  have h_inter_polar : PolarDensity K (S ∩ T) = some (ρS - 0) := by
    have hU : PolarDensity K ((S ∩ T) ∪ (S \ T)) = some ρS := by
      rw [h_union_eq]; exact hS_polar
    exact proposition_21_14c_additive_case3 (S ∩ T) (S \ T) h_inter_fin
      0 ρS h_sdiff_polar hU
  rw [sub_zero] at h_inter_polar
  have h_inter_dir : HasDirichletDensity K (S ∩ T) ρS := by
    have := (polarDensity_eq_some_iff (K := K)).mp h_inter_polar
    exact polar_implies_dirichlet this
  exact ps9_dirichletDensity_mono Set.inter_subset_right h_inter_dir hT_dir

end GlobalCFT

namespace GlobalCFT

/--
[extensionConductor_eq_zero_of_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma extensionConductor_eq_zero_of_unramified
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {𝔭 : Prime' K}
-- given
  (_h : IsUnramifiedIn K L 𝔭) :
-- imply
  (extensionConductor K L) (Place.finite 𝔭) = 0 := by
-- proof
  unfold extensionConductor conductorOfCongruenceSubgroup
  have h_spec := (corollary_22_7 K (extensionAdmissibleModulus K L)
    (extensionNormSubgroup K L) (extensionNormSubgroup_isCong K L)).choose_spec
  have h_dvd : Modulus.dvd
    (corollary_22_7 K (extensionAdmissibleModulus K L)
      (extensionNormSubgroup K L) (extensionNormSubgroup_isCong K L)).choose
    (extensionAdmissibleModulus K L) := by
    exact h_spec.1.2 (extensionAdmissibleModulus K L)
      ⟨extensionNormSubgroup K L, extensionNormSubgroup_isCong K L,
        congruenceSubgroupEquiv_refl K (extensionAdmissibleModulus K L)
          (extensionNormSubgroup K L)⟩
  have h_le := h_dvd (Place.finite 𝔭)
  have h_zero : (extensionAdmissibleModulus K L) (Place.finite 𝔭) = 0 := rfl
  omega

end GlobalCFT

namespace GlobalCFT

/--
[extensionNormSubgroup_equiv_at_modulus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma extensionNormSubgroup_equiv_at_modulus
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {𝔫 : Modulus K} :
-- imply
  ∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫), IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K (extensionAdmissibleModulus K L) 𝔫 (extensionNormSubgroup K L) 𝒟 := by
-- proof
  set 𝔪 := extensionAdmissibleModulus K L
  have h_dvd_m_n : Modulus.dvd 𝔪 𝔫 := fun v => Nat.zero_le _
  set 𝒟 := Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 h_dvd_m_n)
    (extensionNormSubgroup K L)
  refine ⟨𝒟, ?_, ?_⟩
  · constructor
    intro x hx
    show (FracIdealsCoprime.inclusion K 𝔪 𝔫 h_dvd_m_n) x ∈ extensionNormSubgroup K L
    exact (extensionNormSubgroup_isCong K L).contains_ray
      (RayGroup.inclusion_le K 𝔪 𝔫 h_dvd_m_n x hx)
  · refine ⟨𝔫, h_dvd_m_n, fun v => le_refl _, ?_⟩
    show 𝒟 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔫 𝔫 _) 𝒟
    ext x
    simp only [Subgroup.mem_comap]
    constructor
    · intro hx; convert hx using 1
    · intro hx; convert hx using 1

end GlobalCFT

namespace GlobalCFT

/--
[extensionConductor_infinite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma extensionConductor_infinite_zero
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {w : NumberField.InfinitePlace K} :
-- imply
  NumberField.InfinitePlace.IsUnramifiedIn L w → (extensionConductor K L) (Place.infinite w) = 0 := by
-- proof
  intro _
  unfold extensionConductor conductorOfCongruenceSubgroup
  have h_spec := (corollary_22_7 K
    (extensionAdmissibleModulus K L)
    (extensionNormSubgroup K L)
    (extensionNormSubgroup_isCong K L)).choose_spec
  have h_dvd : Modulus.dvd
    (corollary_22_7 K
      (extensionAdmissibleModulus K L)
      (extensionNormSubgroup K L)
      (extensionNormSubgroup_isCong K L)).choose
    (extensionAdmissibleModulus K L) := by
    exact h_spec.1.2 (extensionAdmissibleModulus K L)
      ⟨extensionNormSubgroup K L, extensionNormSubgroup_isCong K L,
        congruenceSubgroupEquiv_refl K (extensionAdmissibleModulus K L)
          (extensionNormSubgroup K L)⟩
  have h_le := h_dvd (Place.infinite w)
  simp only [extensionAdmissibleModulus] at h_le
  exact Nat.le_zero.mp h_le

end GlobalCFT

namespace GlobalCFT

/--
[normGroup_isCongruenceSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma normGroup_isCongruenceSubgroup
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {𝔪 : Modulus K}
-- given
  (h_cond : Modulus.dvd (extensionConductor K L) 𝔪) :
-- imply
  IsCongruenceSubgroup K 𝔪 (NormGroup K L 𝔪) :=
-- proof
  ⟨le_sup_left⟩

end GlobalCFT

namespace GlobalCFT

/--
[choosePrimeOverHOS_lyingUnder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma choosePrimeOverHOS_lyingUnder
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {𝔭 : Prime' K} :
-- imply
  lyingUnder K L (choosePrimeOverHOS K L 𝔭) = 𝔭 := by
-- proof
  ext
  simp only [lyingUnder, IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
    choosePrimeOverHOS, choosePrimeOver_over]

end GlobalCFT

namespace GlobalCFT

/--
[theorem_6_10_norm_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma theorem_6_10_norm_prime
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {𝔮 : Prime' L} :
-- imply
  fracIdealNorm K L (primeAsUnitFracIdeal L 𝔮) = (primeAsUnitFracIdeal K (lyingUnder K L 𝔮)) ^ (inertiaDegree' K L 𝔮) :=
-- proof
fracIdealNorm_prime_eq K L 𝔮

end GlobalCFT

namespace GlobalCFT

/--
[primeAbove_coprime_extendModulus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma primeAbove_coprime_extendModulus
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  {𝔪 : Modulus K}
  {𝔭 : Prime' K}
  {𝔮 : Prime' L}
-- given
  (h_over : lyingUnder K L 𝔮 = 𝔭)
  (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
-- imply
  (extendModulus K L 𝔪) (Place.finite 𝔮) = 0 := by
-- proof
  simp only [extendModulus]
  rw [h_over]
  simp only [Nat.mul_eq_zero]
  exact Or.inr h_coprime

end GlobalCFT

namespace GlobalCFT

/--
[splitsCompletely_inertiaDeg_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma splitsCompletely_inertiaDeg_eq_one
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {𝔭 : Prime' K}
  {𝔮 : Prime' L}
-- given
  (h_split : SplitsCompletely K L 𝔭)
  (h_over : lyingUnder K L 𝔮 = 𝔭) :
-- imply
  inertiaDegree' K L 𝔮 = 1 := by
-- proof
  have h_frob_eq_one : FrobeniusAutomorphism K L 𝔭 = 1 := h_split
  let Q₀ := choosePrimeOver K L 𝔭
  have h_isArith : IsArithFrobAt (NumberField.RingOfIntegers K)
    (arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q₀) Q₀ :=
    IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q₀
  rw [FrobeniusAutomorphism] at h_frob_eq_one
  rw [h_frob_eq_one] at h_isArith
  have h_pow : ∀ x : NumberField.RingOfIntegers L ⧸ Q₀,
    x ^ Nat.card (NumberField.RingOfIntegers K ⧸ Ideal.under (NumberField.RingOfIntegers K) Q₀) = x := by
    intro x
    have := h_isArith.restrict_apply x
    have hrestr_id : ∀ y : NumberField.RingOfIntegers L ⧸ Q₀, h_isArith.restrict y = y := by
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      show Ideal.Quotient.mk Q₀ ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) (1 : L ≃ₐ[K] L)) y) = Ideal.Quotient.mk Q₀ y
      congr 1
    rw [← this, hrestr_id]
  haveI hQ₀_prime : Q₀.IsPrime := choosePrimeOver_isPrime K L 𝔭
  haveI hQ₀_finite : Finite (NumberField.RingOfIntegers L ⧸ Q₀) :=
    choosePrimeOver_finite K L 𝔭
  haveI : Fintype (NumberField.RingOfIntegers L ⧸ Q₀) := Fintype.ofFinite _
  let P₀ := Ideal.under (NumberField.RingOfIntegers K) Q₀
  haveI : Finite (NumberField.RingOfIntegers K ⧸ P₀) :=
    Finite.of_injective _ Ideal.algebraMap_quotient_injective
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ P₀) := Fintype.ofFinite _
  have h_pow_card : ∀ x : NumberField.RingOfIntegers L ⧸ Q₀,
    x ^ Fintype.card (NumberField.RingOfIntegers K ⧸ P₀) = x := by
    intro x
    rw [← Nat.card_eq_fintype_card]
    exact h_pow x
  have hP₀_eq : P₀ = 𝔭.asIdeal := choosePrimeOver_over K L 𝔭
  haveI hQ₀_max : Q₀.IsMaximal :=
    hQ₀_prime.isMaximal (choosePrimeOver_ne_bot K L 𝔭)
  haveI hP₀_max : P₀.IsMaximal := hP₀_eq ▸ (𝔭.isPrime.isMaximal 𝔭.ne_bot)
  letI : Field (NumberField.RingOfIntegers K ⧸ P₀) := Ideal.Quotient.field P₀
  letI : Field (NumberField.RingOfIntegers L ⧸ Q₀) := Ideal.Quotient.field Q₀
  letI : Algebra (NumberField.RingOfIntegers K ⧸ P₀)
    (NumberField.RingOfIntegers L ⧸ Q₀) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq rfl)
  have h_finrank_one : Module.finrank (NumberField.RingOfIntegers K ⧸ P₀)
    (NumberField.RingOfIntegers L ⧸ Q₀) = 1 := by
    have hfrob_eq : FiniteField.frobeniusAlgHom (NumberField.RingOfIntegers K ⧸ P₀)
      (NumberField.RingOfIntegers L ⧸ Q₀) = 1 := by
      apply AlgHom.ext
      intro x
      show x ^ Fintype.card (NumberField.RingOfIntegers K ⧸ P₀) = x
      exact h_pow_card x
    rw [← FiniteField.orderOf_frobeniusAlgHom, hfrob_eq, orderOf_one]
  have h_comap : Ideal.comap (algebraMap (NumberField.RingOfIntegers K)
    (NumberField.RingOfIntegers L)) Q₀ = P₀ := rfl
  have h_inertiaDeg_Q₀ : Ideal.inertiaDeg P₀ Q₀ = 1 := by
    unfold Ideal.inertiaDeg
    simp only [h_comap]
    convert h_finrank_one
  unfold inertiaDegree'
  rw [h_over]
  rw [hP₀_eq] at h_inertiaDeg_Q₀
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  haveI : Finite (NumberField.RingOfIntegers L ⧸ 𝔮.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮.ne_bot
  haveI : Q₀.LiesOver 𝔭.asIdeal := Ideal.LiesOver.mk hP₀_eq.symm
  have h𝔮_over_asIdeal : 𝔭.asIdeal = Ideal.under (NumberField.RingOfIntegers K) 𝔮.asIdeal := by
    have := IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers K) 𝔮
    rw [← this]
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h_over.symm
  haveI : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := Ideal.LiesOver.mk h𝔮_over_asIdeal
  rw [← h_inertiaDeg_Q₀]
  exact (Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal Q₀ 𝔮.asIdeal (L ≃ₐ[K] L)).symm

end GlobalCFT

namespace GlobalCFT

/--
[splitsCompletely_coprime_mem_normGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma splitsCompletely_coprime_mem_normGroup
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {𝔪 : Modulus K}
  {𝔭 : Prime' K}
-- given
  (h_cond : Modulus.dvd (extensionConductor K L) 𝔪)
  (h_split : SplitsCompletely K L 𝔭)
  (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
-- imply
  PrimeToFracIdealsCoprime K 𝔪 𝔭 h_coprime ∈ NormGroup K L 𝔪 := by
-- proof
  let 𝔮 := choosePrimeOverHOS K L 𝔭
  have h_over : lyingUnder K L 𝔮 = 𝔭 := choosePrimeOverHOS_lyingUnder K L 𝔭
  have h_ext_coprime : (extendModulus K L 𝔪) (Place.finite 𝔮) = 0 :=
    primeAbove_coprime_extendModulus K L 𝔪 𝔭 𝔮 h_over h_coprime
  let 𝔮_coprime : FracIdealsCoprime L (extendModulus K L 𝔪) :=
    primeCoprime L (extendModulus K L 𝔪) 𝔮 h_ext_coprime
  have h_f_eq_one : inertiaDegree' K L 𝔮 = 1 :=
    splitsCompletely_inertiaDeg_eq_one K L 𝔭 𝔮 h_split h_over
  have h_norm_eq : fracIdealNorm K L (primeAsUnitFracIdeal L 𝔮) =
    primeAsUnitFracIdeal K 𝔭 := by
    rw [theorem_6_10_norm_prime K L 𝔮, h_over, h_f_eq_one, pow_one]
  have h_in_range : PrimeToFracIdealsCoprime K 𝔪 𝔭 h_coprime ∈
    (idealNormMap K L 𝔪).range := by
    refine ⟨𝔮_coprime, ?_⟩
    apply Subtype.ext
    simp only [idealNormMap, MonoidHom.coe_mk, OneHom.coe_mk]
    exact h_norm_eq
  exact idealNormMap_range_le_normGroup K L 𝔪 h_in_range

end GlobalCFT

namespace GlobalCFT

/--
[proposition_22_28](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma proposition_22_28
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {𝔪 : Modulus K}
-- given
  (h_cond : Modulus.dvd (extensionConductor K L) 𝔪) :
-- imply
  PrimeSetLe (Spl K L) (primesInCongruenceSubgroup K 𝔪 (NormGroup K L 𝔪)) := by
-- proof
  apply Set.Finite.subset (modulus_support_finite K 𝔪)
  intro 𝔭 h𝔭
  simp only [Set.mem_diff, Spl, Set.mem_setOf_eq, primesInCongruenceSubgroup] at h𝔭
  obtain ⟨h_split, h_not_in⟩ := h𝔭
  simp only [Set.mem_setOf_eq]
  intro h_coprime
  apply h_not_in
  exact ⟨h_coprime,
    splitsCompletely_coprime_mem_normGroup K L 𝔪 h_cond 𝔭 h_split h_coprime⟩

end GlobalCFT

/--
[proposition_28_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma proposition_28_3
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K}
  {θ' : IdeleGroup K →* θ.GalAb}
-- given
  (hcompat : ∀ (i : θ.I) (a : IdeleGroup K), θ.proj i (θ' a) = θ.artinMap i a) :
-- imply
  ∀ (a : IdeleGroup K), θ' a = θ.artinHom a := by
-- proof
  intro a
  have h : ∀ i : θ.I, θ.proj i (θ' a * (θ.artinHom a)⁻¹) = 1 := by
    intro i
    rw [map_mul, map_inv]
    rw [hcompat i a, θ.artinMap_eq_proj i a]
    exact mul_inv_cancel _
  have := θ.proj_jointly_injective (θ' a * (θ.artinHom a)⁻¹) h
  rwa [mul_inv_eq_one] at this

/--
[GlobalArtinMap.artinHomCK_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma GlobalArtinMap.artinHomCK_comp
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K}
  {a : IdeleGroup K} :
-- imply
  θ.artinHomCK (QuotientGroup.mk a) = θ.artinHom a := by
-- proof
  simp only [artinHomCK, QuotientGroup.lift_mk']

/--
[GlobalArtinMap.normSubgroupCK_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma GlobalArtinMap.normSubgroupCK_normal
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K}
  {i : θ.I} :
-- imply
  (θ.normSubgroupCK i).Normal :=
-- proof
  θ.normSubgroup_normal i
attribute [instance] GlobalArtinMap.normSubgroupCK_normal

/--
[theorem_28_4_ker_eq_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma theorem_28_4_ker_eq_norm
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K}
  {i : θ.I} :
-- imply
  MonoidHom.ker (θ.artinMapCK i) = θ.normSubgroupCK i :=
-- proof
  θ.ker_eq_normSubgroup i

/--
[theorem_28_4_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma theorem_28_4_iso
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K}
  {i : θ.I} :
-- imply
  Nonempty (IdeleClassGroup K ⧸ θ.normSubgroupCK i ≃* θ.GalLK i) :=
-- proof
  ⟨QuotientGroup.liftEquiv (θ.normSubgroupCK i)
    (θ.artinMapCK_surjective i) (θ.ker_eq_normSubgroup i).symm⟩
section Chebotarev
universe w
open NumberField RayClassField GlobalCFT

/--
[FrobeniusConjClass.nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma FrobeniusConjClass.nonempty
  {K : Type w}
  {L : Type w}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  {𝔭 : Prime' K}
-- given
  (_h_unram : GlobalCFT.IsUnramifiedIn K L 𝔭) :
-- imply
  (FrobeniusConjClass K L 𝔭).Nonempty := by
-- proof
  have h𝔭 := 𝔭.isPrime
  have h_inj := RingOfIntegers.algebraMap.injective K L
  obtain ⟨𝔔, _, h𝔔_prime, h𝔔_comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := RingOfIntegers L) 𝔭.asIdeal ⊥
      (by rw [Ideal.comap_bot_of_injective _ h_inj]; exact bot_le)
  have h𝔔_ne_bot : 𝔔 ≠ ⊥ := by
    intro h
    rw [h, Ideal.comap_bot_of_injective _ h_inj] at h𝔔_comap
    exact 𝔭.ne_bot h𝔔_comap.symm
  haveI : 𝔔.IsMaximal := Ideal.IsPrime.isMaximal h𝔔_prime h𝔔_ne_bot
  haveI : 𝔔.IsPrime := h𝔔_prime
  haveI : Finite (RingOfIntegers L ⧸ 𝔔) := inferInstance
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔
  exact ⟨σ, 𝔔, h𝔔_prime, ⟨h𝔔_comap.symm⟩, hσ⟩

/--
[rayGroup_isCongruenceSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma rayGroup_isCongruenceSubgroup
  {K : Type w}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  IsCongruenceSubgroup K 𝔪 (RayGroup K 𝔪) :=
-- proof
  ⟨le_refl _⟩

/--
[rayGroup_index_eq_natCard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma rayGroup_index_eq_natCard
  {K : Type w}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  (RayGroup K 𝔪).index = Nat.card (RayClassGroup K 𝔪) := by
-- proof
  rw [Subgroup.index_eq_card]
  rfl

/--
[dirichletDensity_disjoint_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma dirichletDensity_disjoint_union
  {K : Type w}
  {L : Type w}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  {A B : Set (L ≃ₐ[K] L)}
  {dA dB : ℚ}
-- given
  (hA : IsConjugationStable A)
  (hB : IsConjugationStable B)
  (h_disj : Disjoint A B)
  (hdA : HasDirichletDensity K (primesWithFrobInSet K L A) dA)
  (hdB : HasDirichletDensity K (primesWithFrobInSet K L B) dB) :
-- imply
  HasDirichletDensity K (primesWithFrobInSet K L (A ∪ B)) (dA + dB) := by
-- proof
  have h_set : primesWithFrobInSet K L (A ∪ B) =
    primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B := by
    ext 𝔭
    simp only [primesWithFrobInSet, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h_unram, h_sub⟩
      obtain ⟨σ, hσ⟩ := FrobeniusConjClass.nonempty K L 𝔭 h_unram
      have frob_conj : ∀ τ, τ ∈ FrobeniusConjClass K L 𝔭 →
        ∃ g : L ≃ₐ[K] L, τ = g * σ * g⁻¹ := by
        intro τ hτ
        obtain ⟨𝔔₁, h𝔔₁_prime, h𝔔₁_over, h𝔔₁_frob⟩ := hσ
        obtain ⟨𝔔₂, h𝔔₂_prime, h𝔔₂_over, h𝔔₂_frob⟩ := hτ
        haveI : 𝔔₁.IsPrime := h𝔔₁_prime
        haveI : 𝔔₂.IsPrime := h𝔔₂_prime
        have h_under_eq : 𝔔₁.under (RingOfIntegers K) = 𝔔₂.under (RingOfIntegers K) := by
          rw [← h𝔔₁_over.over, ← h𝔔₂_over.over]
        obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
          (RingOfIntegers K) (RingOfIntegers L) (L ≃ₐ[K] L) 𝔔₁ 𝔔₂ h_under_eq
        have h_conj_frob : IsArithFrobAt (RingOfIntegers K) (g * σ * g⁻¹) 𝔔₂ :=
          hg ▸ h𝔔₁_frob.conj g
        haveI : Algebra.IsUnramifiedAt (RingOfIntegers K) 𝔔₂ := h_unram 𝔔₂ h𝔔₂_over
        have hQ : 𝔔₂.primeCompl ≤ nonZeroDivisors (RingOfIntegers L) :=
          Ideal.primeCompl_le_nonZeroDivisors 𝔔₂
        have h_alg_eq := h𝔔₂_frob.eq_of_isUnramifiedAt h_conj_frob hQ
        haveI : FaithfulSMul (L ≃ₐ[K] L) (RingOfIntegers L) := by
          constructor
          intro σ' τ' h'
          have hL : ∀ (a : RingOfIntegers L), σ' (a : L) = τ' (a : L) :=
            fun a => congr_arg Subtype.val (h' a)
          have h_ring : σ'.toRingHom.comp (algebraMap (RingOfIntegers L) L) =
            τ'.toRingHom.comp (algebraMap (RingOfIntegers L) L) :=
            RingHom.ext fun a => hL a
          exact AlgEquiv.ext fun x => RingHom.congr_fun
            (IsLocalization.ringHom_ext (nonZeroDivisors (RingOfIntegers L)) h_ring) x
        exact ⟨g, MulSemiringAction.toAlgHom_injective
          (RingOfIntegers K) (RingOfIntegers L) h_alg_eq⟩
      cases h_sub hσ with
      | inl hσ_A =>
        left; exact ⟨h_unram, fun τ hτ => by
          obtain ⟨g, hg⟩ := frob_conj τ hτ; rw [hg]; exact hA g σ hσ_A⟩
      | inr hσ_B =>
        right; exact ⟨h_unram, fun τ hτ => by
          obtain ⟨g, hg⟩ := frob_conj τ hτ; rw [hg]; exact hB g σ hσ_B⟩
    · rintro (⟨h_unram, h_sub_A⟩ | ⟨h_unram, h_sub_B⟩)
      · exact ⟨h_unram, h_sub_A.trans Set.subset_union_left⟩
      · exact ⟨h_unram, h_sub_B.trans Set.subset_union_right⟩
  have h_disj_primes : Disjoint (primesWithFrobInSet K L A) (primesWithFrobInSet K L B) := by
    rw [Set.disjoint_iff]
    intro 𝔭 ⟨h𝔭_A, h𝔭_B⟩
    obtain ⟨h_unram, h_sub_A⟩ := h𝔭_A
    obtain ⟨_, h_sub_B⟩ := h𝔭_B
    obtain ⟨σ, hσ⟩ := FrobeniusConjClass.nonempty K L 𝔭 h_unram
    exact Set.disjoint_iff.mp h_disj ⟨h_sub_A hσ, h_sub_B hσ⟩
  rw [h_set]
  show HasDirichletDensity K
    (primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B) (dA + dB)
  unfold HasDirichletDensity
  rw [show ((dA + dB : ℚ) : ℝ) = (↑dA : ℝ) + (↑dB : ℝ) from by push_cast; ring]
  have h_ev_eq : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
    (fun s => (∑' (𝔭 : ↑(primesWithFrobInSet K L A)),
      ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
      Real.log (1 / (s - 1)) +
      (∑' (𝔭 : ↑(primesWithFrobInSet K L B)),
        ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
        Real.log (1 / (s - 1))) s =
    (fun s => (∑' (𝔭 : ↑(primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B)),
      ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
      Real.log (1 / (s - 1))) s := by
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro s (hs : 1 < s)
    dsimp only
    rw [← add_div]
    congr 1
    let f : Prime' K → ℝ := fun 𝔭 => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
    have hsumA : Summable (f ∘ Subtype.val (p := (· ∈ primesWithFrobInSet K L A))) :=
      summable_rpow_inv_absNorm_prime (primesWithFrobInSet K L A) s hs
    have hsumB : Summable (f ∘ Subtype.val (p := (· ∈ primesWithFrobInSet K L B))) :=
      summable_rpow_inv_absNorm_prime (primesWithFrobInSet K L B) s hs
    exact (Summable.tsum_union_disjoint h_disj_primes hsumA hsumB).symm
  exact (Filter.Tendsto.add hdA hdB).congr' h_ev_eq

/--
[primesWithFrobInSet_empty_hasDensity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma primesWithFrobInSet_empty_hasDensity_zero
  {K : Type w}
  {L : Type w}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L] :
-- imply
  HasDirichletDensity K (primesWithFrobInSet K L ∅) 0 := by
-- proof
  have h_empty : primesWithFrobInSet K L ∅ = ∅ := by
    ext 𝔭
    simp only [primesWithFrobInSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h_unram h_sub
    exact (FrobeniusConjClass.nonempty K L 𝔭 h_unram).ne_empty (Set.subset_empty_iff.mp h_sub)
  unfold HasDirichletDensity
  have h_tsum : ∀ s : ℝ, ∑' (𝔭 : ↥(primesWithFrobInSet K L ∅)),
    ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) = 0 := by
    intro s
    rwa [h_empty]
  simp_rw [h_tsum, zero_div]
  simp only [Rat.cast_zero]
  exact tendsto_const_nhds

/--
[conjClass_subset_of_mem_conjStable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma conjClass_subset_of_mem_conjStable
  [Group G]
  {C : Set G}
  {σ : G}
-- given
  (hC : IsConjugationStable C)
  (hσ : σ ∈ C) :
-- imply
  (ConjClasses.mk σ).carrier ⊆ C := by
-- proof
  intro τ hτ
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hτ
  have hconj : IsConj τ σ := ConjClasses.mk_eq_mk_iff_isConj.mp hτ
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have h1 : τ = g⁻¹ * σ * (g⁻¹)⁻¹ := by
    calc τ = g⁻¹ * (g * τ * g⁻¹) * (g⁻¹)⁻¹ := by group
    _ = g⁻¹ * σ * (g⁻¹)⁻¹ := by rw [hg]
  rw [h1]
  exact hC g⁻¹ σ hσ

/--
[conjStable_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma conjStable_sdiff
  [Group G]
  {C : Set G}
  {σ : G}
-- given
  (hC : IsConjugationStable C) :
-- imply
  IsConjugationStable (C \ (ConjClasses.mk σ).carrier) := by
-- proof
  intro g c ⟨hcC, hcCC⟩
  refine ⟨hC g c hcC, ?_⟩
  intro hmem
  apply hcCC
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hmem ⊢
  rw [← hmem]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)
end Chebotarev
section Functoriality
variable {K : Type*} [Field K] [NumberField K]
  {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
open Ideles

/--
[normSubgroup_finiteIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma normSubgroup_finiteIndex
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K}
  {i : θ.I} :
-- imply
  (θ.normSubgroupCK i).FiniteIndex := by
-- proof
  have hker : MonoidHom.ker (θ.artinMapCK i) = θ.normSubgroupCK i :=
    theorem_28_4_ker_eq_norm θ i
  rw [← hker]
  exact Subgroup.finiteIndex_ker (θ.artinMapCK i)

/--
[artinMap_quotient_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
lemma artinMap_quotient_iso
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K}
  {i : θ.I} :
-- imply
  Nonempty (IdeleClassGroup K ⧸ θ.normSubgroupCK i ≃* θ.GalLK i) :=
-- proof
  theorem_28_4_iso θ i
end

/--
[FracIdealsCoprime_subgroup_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma FracIdealsCoprime_subgroup_le_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
-- given
  (h : Modulus.dvd 𝔪 𝔫) :
-- imply
  FracIdealsCoprime_subgroup K 𝔫 ≤ FracIdealsCoprime_subgroup K 𝔪 := by
-- proof
  apply GlobalCFT.FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h

/--
[IsRayGenerator_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma IsRayGenerator_inclusion_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {I : FracIdealsCoprime K 𝔫}
-- given
  (h : Modulus.dvd 𝔪 𝔫)
  (hI : IsRayGenerator 𝔫 I) :
-- imply
  IsRayGenerator 𝔪 (Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h) I) := by
-- proof
  apply GlobalCFT.IsRayGenerator_inclusion K 𝔪 𝔫 h I hI

/--
[RayGroup.inclusion_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma inclusion_le_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
-- given
  (h : Modulus.dvd 𝔪 𝔫) :
-- imply
  ∀ x : FracIdealsCoprime K 𝔫, x ∈ RayGroup K 𝔫 → (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) x ∈ RayGroup K 𝔪 := by
-- proof
  apply GlobalCFT.RayGroup.inclusion_le K 𝔪 𝔫 h

/--
[congruenceSubgroupEquiv_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma congruenceSubgroupEquiv_refl_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)} :
-- imply
  CongruenceSubgroupEquiv K 𝔪 𝔪 𝒞 𝒞 := by
-- proof
  apply GlobalCFT.congruenceSubgroupEquiv_refl K 𝔪 𝒞

/--
[congruenceSubgroupEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma congruenceSubgroupEquiv_symm_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)}
  {𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)}
-- given
  (h : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
-- imply
  CongruenceSubgroupEquiv K 𝔪₂ 𝔪₁ 𝒞₂ 𝒞₁ := by
-- proof
  apply GlobalCFT.congruenceSubgroupEquiv_symm K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ h

/--
[FracIdealsCoprime.inclusion_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma inclusion_comp_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 𝔭 : Modulus K}
-- given
  (h₁ : Modulus.dvd 𝔪 𝔫)
  (h₂ : Modulus.dvd 𝔫 𝔭)
  (h₃ : Modulus.dvd 𝔪 𝔭) :
-- imply
  ∀ x : FracIdealsCoprime K 𝔭, (FracIdealsCoprime.inclusion K 𝔪 𝔫 h₁) ((FracIdealsCoprime.inclusion K 𝔫 𝔭 h₂) x) = (FracIdealsCoprime.inclusion K 𝔪 𝔭 h₃) x := by
-- proof
  apply GlobalCFT.FracIdealsCoprime.inclusion_comp K 𝔪 𝔫 𝔭 h₁ h₂ h₃

/--
[FracIdealsCoprime.exists_ray_mul_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma exists_ray_mul_coprime_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {x : FracIdealsCoprime K 𝔪}
-- given
  (h : Modulus.dvd 𝔪 𝔫) :
-- imply
  ∃ (r : FracIdealsCoprime K 𝔪), r ∈ RayGroup K 𝔪 ∧ (x * r⁻¹).val ∈ FracIdealsCoprime_subgroup K 𝔫 := by
-- proof
  apply GlobalCFT.FracIdealsCoprime.exists_ray_mul_coprime K 𝔪 𝔫 h x

/--
[FracIdealsCoprime.approx_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma approx_theorem_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {x : FracIdealsCoprime K 𝔪}
-- given
  (h : Modulus.dvd 𝔪 𝔫) :
-- imply
  ∃ (y : FracIdealsCoprime K 𝔫) (r : FracIdealsCoprime K 𝔪), r ∈ RayGroup K 𝔪 ∧ x = (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) y * r := by
-- proof
  apply GlobalCFT.FracIdealsCoprime.approx_theorem K 𝔪 𝔫 h x

/--
[FracIdealsCoprime.inclusion_mk_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma inclusion_mk_surjective_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  [𝒞.Normal]
-- given
  (h : Modulus.dvd 𝔪 𝔫)
  (hCong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  Function.Surjective ((QuotientGroup.mk' 𝒞).comp (FracIdealsCoprime.inclusion K 𝔪 𝔫 h)) := by
-- proof
  apply GlobalCFT.FracIdealsCoprime.inclusion_mk_surjective K 𝔪 𝔫 h 𝒞 hCong

/--
[congruenceSubgroupEquiv_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma congruenceSubgroupEquiv_trans_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ 𝔪₃ : Modulus K}
  {𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)}
  {𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)}
  {𝒞₃ : Subgroup (FracIdealsCoprime K 𝔪₃)}
-- given
  (h₁₂ : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂)
  (h₂₃ : CongruenceSubgroupEquiv K 𝔪₂ 𝔪₃ 𝒞₂ 𝒞₃) :
-- imply
  CongruenceSubgroupEquiv K 𝔪₁ 𝔪₃ 𝒞₁ 𝒞₃ := by
-- proof
  apply GlobalCFT.congruenceSubgroupEquiv_trans K 𝔪₁ 𝔪₂ 𝔪₃ 𝒞₁ 𝒞₂ 𝒞₃ h₁₂ h₂₃

/--
[FracIdealsCoprime.subtype_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma subtype_inclusion_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {x : FracIdealsCoprime K 𝔫}
-- given
  (h : Modulus.dvd 𝔪 𝔫) :
-- imply
  (FracIdealsCoprime_subgroup K 𝔪).subtype (FracIdealsCoprime.inclusion K 𝔪 𝔫 h x) = (FracIdealsCoprime_subgroup K 𝔫).subtype x := by
-- proof
  apply GlobalCFT.FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 h x

/--
[mem_comap_inclusion_iff_mem_toAmbientSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma mem_comap_inclusion_iff_mem_toAmbientSubgroup_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {x : FracIdealsCoprime K 𝔫}
-- given
  (h : Modulus.dvd 𝔪 𝔫) :
-- imply
  x ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) 𝒞 ↔ (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈ 𝒞.map (FracIdealsCoprime_subgroup K 𝔪).subtype := by
-- proof
  apply GlobalCFT.mem_comap_inclusion_iff_mem_toAmbientSubgroup K 𝔪 𝔫 h 𝒞 x

/--
[isEquiv_to_congruenceSubgroupEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma isEquiv_to_congruenceSubgroupEquiv_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)}
  {𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)}
-- given
  (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
  (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
  (h_isEquiv : (⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩) :
-- imply
  CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ := by
-- proof
  apply GlobalCFT.isEquiv_to_congruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ h₁ h₂ h_isEquiv

/--
[isEquiv_of_dvd_comap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma isEquiv_of_dvd_comap_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {𝒞_𝔫 : Subgroup (FracIdealsCoprime K 𝔫)}
-- given
  (hdvd : Modulus.dvd 𝔪 𝔫)
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (h_cong_𝔫 : IsCongruenceSubgroup K 𝔫 𝒞_𝔫)
  (h_eq : 𝒞_𝔫 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd) 𝒞) :
-- imply
  (⟨𝔪, 𝒞, h_cong.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv ⟨𝔫, 𝒞_𝔫, h_cong_𝔫.contains_ray⟩ := by
-- proof
  apply GlobalCFT.isEquiv_of_dvd_comap K 𝔪 𝔫 hdvd 𝒞 h_cong 𝒞_𝔫 h_cong_𝔫 h_eq

/--
[congruenceSubgroupEquiv_to_isEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma congruenceSubgroupEquiv_to_isEquiv_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)}
  {𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)}
-- given
  (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
  (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
  (h_equiv : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
-- imply
  (⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩ := by
-- proof
  apply GlobalCFT.congruenceSubgroupEquiv_to_isEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ h₁ h₂ h_equiv

/--
[proposition_22_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma proposition_22_6_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
  {𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)}
  {𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)}
-- given
  (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
  (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
  (h_equiv : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
-- imply
  ∃ 𝒞 : Subgroup (FracIdealsCoprime K (Modulus.gcd 𝔪₁ 𝔪₂)), IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 ∧ CongruenceSubgroupEquiv K 𝔪₁ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₁ 𝒞 ∧ CongruenceSubgroupEquiv K 𝔪₂ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₂ 𝒞 := by
-- proof
  apply GlobalCFT.proposition_22_6 K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ h₁ h₂ h_equiv

/--
[equiv_moduli_closed_under_gcd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma equiv_moduli_closed_under_gcd_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h₁ : ∃ 𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁), IsCongruenceSubgroup K 𝔪₁ 𝒞₁ ∧ CongruenceSubgroupEquiv K 𝔪 𝔪₁ 𝒞 𝒞₁)
  (h₂ : ∃ 𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂), IsCongruenceSubgroup K 𝔪₂ 𝒞₂ ∧ CongruenceSubgroupEquiv K 𝔪 𝔪₂ 𝒞 𝒞₂) :
-- imply
  ∃ 𝒞g : Subgroup (FracIdealsCoprime K (Modulus.gcd 𝔪₁ 𝔪₂)), IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞g ∧ CongruenceSubgroupEquiv K 𝔪 (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 𝒞g := by
-- proof
  apply GlobalCFT.equiv_moduli_closed_under_gcd K 𝔪 𝒞 𝔪₁ 𝔪₂ h₁ h₂

/--
[gcd_weight_lt_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma gcd_weight_lt_of_not_dvd_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h : ¬ 𝔪₁.dvd 𝔪₂) :
-- imply
  (𝔪₁.gcd 𝔪₂).weight < 𝔪₁.weight := by
-- proof
  apply GlobalCFT.gcd_weight_lt_of_not_dvd h

/--
[exists_minimal_equiv_modulus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma exists_minimal_equiv_modulus_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  ∃ (𝔠 : Modulus K), (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠), IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧ ∀ (𝔫 : Modulus K), (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫), IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) → Modulus.dvd 𝔠 𝔫 := by
-- proof
  apply GlobalCFT.exists_minimal_equiv_modulus K 𝔪 𝒞 h_cong

/--
[corollary_22_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma corollary_22_7_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  ∃! (𝔠 : Modulus K), (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠), IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧ ∀ (𝔫 : Modulus K), (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫), IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) → Modulus.dvd 𝔠 𝔫 := by
-- proof
  apply GlobalCFT.corollary_22_7 K 𝔪 𝒞 h_cong

/--
[kernelCongruenceSubgroup_isCong](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma kernelCongruenceSubgroup_isCong_eq
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {χ : RayClassCharacter K 𝔪} :
-- imply
  IsCongruenceSubgroup K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ) := by
-- proof
  apply GlobalCFT.kernelCongruenceSubgroup_isCong K 𝔪 χ

/--
[extensionNormSubgroup_isCong](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma extensionNormSubgroup_isCong_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L] :
-- imply
  IsCongruenceSubgroup K (extensionAdmissibleModulus K L) (extensionNormSubgroup K L) := by
-- proof
  apply GlobalCFT.extensionNormSubgroup_isCong K L

/--
[theorem_28_4_principal_in_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean)
-/
@[path]
private lemma theorem_28_4_principal_in_ker_eq
  [Field K]
  [NumberField K]
  {θ : GlobalArtinMap K} :
-- imply
  principalIdeles K ≤ MonoidHom.ker θ.artinHom := by
-- proof
  apply theorem_28_4_principal_in_ker θ


-- created on 2026-10-23
