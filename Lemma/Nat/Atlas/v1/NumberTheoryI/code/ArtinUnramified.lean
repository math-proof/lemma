import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ArtinUnramified
open NumberField ArtinUnramified
open scoped Pointwise
open nonZeroDivisors


namespace ArtinUnramified

/--
[hilbert_theorem_90](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma hilbert_theorem_90
  {K L : Type}
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  [IsCyclic (L ≃ₐ[K] L)]
  {σ : L ≃ₐ[K] L}
  {α : L}
-- given
  (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ) :
-- imply
  Algebra.norm K α = 1 ↔ ∃ β : Lˣ, (↑β : L) / σ (↑β : L) = α := by
-- proof
  constructor
  · exact groupCohomology.exists_div_of_norm_eq_one hσ
  · rintro ⟨β, rfl⟩
    rw [div_eq_mul_inv]
    simp only [map_mul, Algebra.norm_inv, Algebra.norm_eq_of_algEquiv]
    exact mul_inv_cancel₀ (Algebra.norm_ne_zero_iff.2 β.isUnit.ne_zero)
section CyclicCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

end ArtinUnramified

namespace ArtinUnramified

/--
[zpow_apply_eq_of_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma zpow_apply_eq_of_apply_eq
  [Field K]
  [Field L]
  [Algebra K L]
  {σ : L ≃ₐ[K] L}
  {x : L}
  {n : ℤ}
-- given
  (h : σ x = x) :
-- imply
  (σ ^ n) x = x := by
-- proof
  induction n with
  | zero => simp
  | succ n ih => rw [zpow_add, zpow_one, AlgEquiv.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub, zpow_one, AlgEquiv.mul_apply]
    have : (σ⁻¹ : L ≃ₐ[K] L) x = x := by
      change σ.symm x = x; rw [AlgEquiv.symm_apply_eq]; exact h.symm
    rw [this, ih]

end ArtinUnramified

namespace ArtinUnramified

/--
[range_sigmaMinusOneMap_le_ker_trace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma range_sigmaMinusOneMap_le_ker_trace
  [Field K]
  [Field L]
  [Algebra K L]
  {σ : L ≃ₐ[K] L} :
-- imply
  LinearMap.range (sigmaMinusOneMap σ) ≤ LinearMap.ker (Algebra.trace K L) := by
-- proof
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  simp only [LinearMap.mem_ker, sigmaMinusOneMap, LinearMap.sub_apply, LinearMap.id_apply,
    AlgEquiv.toLinearMap_apply, map_sub, Algebra.trace_eq_of_algEquiv, sub_self]

end ArtinUnramified

namespace ArtinUnramified

/--
[finrank_ker_sigmaMinusOneMap_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma finrank_ker_sigmaMinusOneMap_eq_one
  [Field K]
  [Field L]
  [Algebra K L]
  {σ : L ≃ₐ[K] L}
-- given
  (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ) :
-- imply
  Module.finrank K (LinearMap.ker (sigmaMinusOneMap σ)) = 1 := by
-- proof
  have h_eq : LinearMap.ker (sigmaMinusOneMap σ) =
    (⊥ : IntermediateField K L).toSubalgebra.toSubmodule := by
    ext x
    simp only [LinearMap.mem_ker, sigmaMinusOneMap, LinearMap.sub_apply, AlgEquiv.toLinearMap_apply,
      LinearMap.id_apply, sub_eq_zero]
    constructor
    · intro h
      have : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
        rw [IntermediateField.mem_fixedField_iff]
        intro g _; obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hσ g)
        exact zpow_apply_eq_of_apply_eq h n
      rw [IsGalois.fixedField_top] at this; exact this
    · intro h
      have hbot : x ∈ (⊥ : IntermediateField K L) := h
      rw [IntermediateField.mem_bot] at hbot
      obtain ⟨k, rfl⟩ := hbot; exact AlgEquiv.commutes σ k
  rw [h_eq]; exact IntermediateField.finrank_bot

end ArtinUnramified

namespace ArtinUnramified

/--
[finrank_range_trace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma finrank_range_trace
  [Field K]
  [Field L]
  [Algebra K L] :
-- imply
  Module.finrank K (LinearMap.range (Algebra.trace K L)) = 1 := by
-- proof
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)]
  simp

end ArtinUnramified

namespace ArtinUnramified

/--
[trace_surjective_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma trace_surjective_cyclic
  [Field K]
  [Field L]
  [Algebra K L]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  [IsCyclic (L ≃ₐ[K] L)] :
-- imply
  Function.Surjective (Algebra.trace K L) :=
-- proof
  Algebra.trace_surjective K L

end ArtinUnramified

namespace ArtinUnramified

/--
[ker_trace_eq_range_sigmaMinusOne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma ker_trace_eq_range_sigmaMinusOne
  [Field K]
  [Field L]
  [Algebra K L]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  [IsCyclic (L ≃ₐ[K] L)]
  {σ : L ≃ₐ[K] L}
  {x : L}
-- given
  (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ)
  (hx : Algebra.trace K L x = 0) :
-- imply
  ∃ y : L, σ y - y = x := by
-- proof
  have hle := range_sigmaMinusOneMap_le_ker_trace (K := K) (L := L) σ
  have hker1 := finrank_ker_sigmaMinusOneMap_eq_one (K := K) (L := L) hσ
  have hrank_rng : Module.finrank K (LinearMap.range (sigmaMinusOneMap σ)) =
    Module.finrank K L - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker (sigmaMinusOneMap σ)
    omega
  have hrank_ker : Module.finrank K (LinearMap.ker (Algebra.trace K L)) =
    Module.finrank K L - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
    have := finrank_range_trace (K := K) (L := L)
    omega
  have heq : LinearMap.range (sigmaMinusOneMap σ) = LinearMap.ker (Algebra.trace K L) :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hx_ker : x ∈ LinearMap.ker (Algebra.trace K L) := LinearMap.mem_ker.mpr hx
  rw [← heq] at hx_ker
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx_ker
  refine ⟨y, ?_⟩
  simp only [sigmaMinusOneMap, LinearMap.sub_apply, AlgEquiv.toLinearMap_apply,
    LinearMap.id_apply] at hy
  exact hy

end ArtinUnramified

namespace ArtinUnramified

/--
[galois_fixed_point_in_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma galois_fixed_point_in_base
  [Field K]
  [Field L]
  [Algebra K L]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  [IsCyclic (L ≃ₐ[K] L)]
  {σ : L ≃ₐ[K] L}
  {x : L}
-- given
  (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ)
  (hx_fixed : σ x = x) :
-- imply
  ∃ k : K, algebraMap K L k = x := by
-- proof
  have : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g _; obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hσ g)
    exact zpow_apply_eq_of_apply_eq hx_fixed n
  rw [IsGalois.fixedField_top] at this
  rwa [IntermediateField.mem_bot] at this

end ArtinUnramified

namespace ArtinUnramified

/--
[norm_one_iff_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma norm_one_iff_quotient
  [Field K]
  [Field L]
  [Algebra K L]
  {K L : Type}
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  [IsCyclic (L ≃ₐ[K] L)]
  {σ : L ≃ₐ[K] L}
  {α : L}
-- given
  (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ)
  (hα : Algebra.norm K α = 1) :
-- imply
  ∃ β : Lˣ, (↑β : L) / σ (↑β : L) = α :=
-- proof
  groupCohomology.exists_div_of_norm_eq_one hσ hα

end ArtinUnramified

namespace ArtinUnramified

/--
[tate_cohomology_cyclic_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma tate_cohomology_cyclic_extension
  [Field K]
  [Field L]
  [Algebra K L]
  {K L : Type}
  [Field K]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  [IsCyclic (L ≃ₐ[K] L)]
  {σ : L ≃ₐ[K] L}
-- given
  (hσ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ) :
-- imply
  Function.Surjective (Algebra.trace K L) ∧ (∀ {x : L}, Algebra.trace K L x = 0 → ∃ y : L, σ y - y = x) ∧ (∀ {x : L}, σ x = x → ∃ k : K, algebraMap K L k = x) ∧ (∀ {α : L}, Algebra.norm K α = 1 → ∃ β : Lˣ, (↑β : L) / σ (↑β : L) = α) :=
-- proof
  ⟨trace_surjective_cyclic K L,
    fun hx => ker_trace_eq_range_sigmaMinusOne K L hσ hx,
    fun hx => galois_fixed_point_in_base K L hσ hx,
    fun hα => norm_one_iff_quotient K L hσ hα⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[normUnitsIndex_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma normUnitsIndex_pos
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L] :
-- imply
  0 < normUnitsIndex K L := by
-- proof
  unfold normUnitsIndex
  set n := Module.finrank K L with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
  haveI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  have hfin : (powMonoidHom (α := (𝓞 K)ˣ) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K)ˣ hn_ne
  have hle : (powMonoidHom (α := (𝓞 K)ˣ) n).range ≤ normImageUnits K L := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    simp only [normImageUnits, Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨Units.map (algebraMap K L).toMonoidHom
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom v), ?_⟩
    ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Units.val_pow_eq_pow_val, map_pow]
    exact Algebra.norm_algebraMap _
  haveI : (normImageUnits K L).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

end ArtinUnramified

namespace ArtinUnramified

/--
[normIntegerUnits_le_normImageUnits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma normIntegerUnits_le_normImageUnits
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L] :
-- imply
  normIntegerUnits K L ≤ normImageUnits K L := by
-- proof
  intro u hu
  simp only [normImageUnits, Subgroup.mem_comap, MonoidHom.mem_range] at hu ⊢
  simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  exact ⟨Units.map (algebraMap (𝓞 L) L).toMonoidHom v, hv⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[normIntegerUnits_index_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma normIntegerUnits_index_pos
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  [IsCyclic (L ≃ₐ[K] L)] :
-- imply
  0 < (normIntegerUnits K L).index := by
-- proof
  set n := Module.finrank K L with hn_def
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp Module.finrank_pos
  haveI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  have hfin : (powMonoidHom (α := (𝓞 K)ˣ) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K)ˣ hn_ne
  have hle_int : (powMonoidHom (α := (𝓞 K)ˣ) n).range ≤ normIntegerUnits K L := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom v, ?_⟩
    ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.coe_comp,
      Function.comp_apply, Units.val_pow_eq_pow_val, map_pow]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact Algebra.norm_algebraMap _
  haveI : (normIntegerUnits K L).FiniteIndex := Subgroup.finiteIndex_of_le hle_int
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

end ArtinUnramified

namespace ArtinUnramified

/--
[herbrand_quotient_computation_ch23](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma herbrand_quotient_computation_ch23
-- imply
  ∀ (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)], ∃ (h0 h_minus1 : ℕ), 0 < h_minus1 ∧ Nat.Coprime h0 h_minus1 ∧ h0 * Module.finrank K L = h_minus1 * e_inf K L := by
-- proof
  intro K L _ _ _ _ _ _ _ _
  set n := Module.finrank K L
  set e := e_inf K L
  have hn : 0 < n := Module.finrank_pos
  have hg : 0 < Nat.gcd e n := by
    obtain h | h := Nat.eq_zero_or_pos (Nat.gcd e n)
    · simp [Nat.eq_zero_of_gcd_eq_zero_right h] at hn
    · exact h
  refine ⟨e / Nat.gcd e n, n / Nat.gcd e n, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right e n)) hg
  · exact Nat.coprime_div_gcd_div_gcd hg
  · rw [Nat.div_mul_right_comm (Nat.gcd_dvd_left e n),
    Nat.div_mul_right_comm (Nat.gcd_dvd_right e n)]
    congr 1
    exact mul_comm e n

end ArtinUnramified

namespace ArtinUnramified

/--
[normIntegerUnits_relIndex_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma normIntegerUnits_relIndex_pos
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  [IsCyclic (L ≃ₐ[K] L)] :
-- imply
  0 < (normIntegerUnits K L).relIndex (normImageUnits K L) := by
-- proof
  set n := Module.finrank K L with hn_def
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp Module.finrank_pos
  haveI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  have hfin : (powMonoidHom (α := (𝓞 K)ˣ) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K)ˣ hn_ne
  have hle_int : (powMonoidHom (α := (𝓞 K)ˣ) n).range ≤ normIntegerUnits K L := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom v, ?_⟩
    ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.coe_comp,
      Function.comp_apply, Units.val_pow_eq_pow_val, map_pow]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact Algebra.norm_algebraMap _
  haveI : (normIntegerUnits K L).FiniteIndex := Subgroup.finiteIndex_of_le hle_int
  haveI : (normIntegerUnits K L).IsFiniteRelIndex (normImageUnits K L) := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]; exact inferInstance
  exact Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero

end ArtinUnramified

namespace ArtinUnramified

/--
[CyclicExtensionData.norm_index_IK_pos_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma CyclicExtensionData.norm_index_IK_pos_ax
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  [IsCyclic (L ≃ₐ[K] L)] :
-- imply
  0 < CyclicExtensionData.norm_index_IK_ax K L :=
-- proof
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
section GaloisUnitsAction
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

end ArtinUnramified

namespace ArtinUnramified

/--
[infinitePlace_map_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma infinitePlace_map_prod
  [Field L]
  [NumberField L]
  {w : InfinitePlace L}
  {s : Finset ι}
  {f : ι → L} :
-- imply
  w (∏ i ∈ s, f i) = ∏ i ∈ s, w (f i) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty => simp [map_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, map_mul, ih, Finset.prod_insert ha]

end ArtinUnramified

namespace ArtinUnramified

/--
[infinitePlace_prod_units](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma infinitePlace_prod_units
  [Field L]
  [NumberField L]
  {w : InfinitePlace L}
  {s : Finset ι}
  {f : ι → (𝓞 L)ˣ} :
-- imply
  w ((algebraMap (𝓞 L) L) ↑(∏ i ∈ s, f i)) = ∏ i ∈ s, w ((algebraMap (𝓞 L) L) ↑(f i)) := by
-- proof
  have hcoe := map_prod ((algebraMap (𝓞 L) L).toMonoidHom.comp (Units.coeHom (𝓞 L))) f s
  simp only [MonoidHom.coe_comp, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Function.comp_def, Units.coeHom_apply] at hcoe
  rw [hcoe]
  exact infinitePlace_map_prod w s _

end ArtinUnramified

namespace ArtinUnramified

/--
[infinitePlace_unit_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma infinitePlace_unit_pos
  [Field L]
  [NumberField L]
  {w : InfinitePlace L}
  {u : (𝓞 L)ˣ} :
-- imply
  0 < w ((algebraMap (𝓞 L) L) ↑u) := by
-- proof
  apply AbsoluteValue.pos
  intro h
  exact Units.ne_zero u (IsFractionRing.injective (𝓞 L) L h)

end ArtinUnramified

namespace ArtinUnramified

/--
[prop_15_9_raw_units](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma prop_15_9_raw_units
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L] :
-- imply
  ∃ u : InfinitePlace L → (𝓞 L)ˣ, (∀ (v w : InfinitePlace L), w ≠ v → w (u v) < 1) := by
-- proof
  have h : ∀ v : InfinitePlace L, ∃ uv : (𝓞 L)ˣ,
    ∀ w : InfinitePlace L, w ≠ v → w uv < 1 := by
    intro v
    obtain ⟨uv, huv⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit L v
    exact ⟨uv, fun w hw => by
      have hpos := NumberField.Units.pos_at_place uv w
      exact Real.log_neg_iff hpos |>.mp (huv w hw)⟩
  choose u hu using h
  exact ⟨u, hu⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[infinitePlace_smul_galActsOnUnits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma infinitePlace_smul_galActsOnUnits
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  {σ : L ≃ₐ[K] L}
  {w : InfinitePlace L}
  {u : (𝓞 L)ˣ} :
-- imply
  w (σ • u : (𝓞 L)ˣ) = (σ⁻¹ • w) u := by
-- proof
  show w ((σ • u : (𝓞 L)ˣ) : L) = (σ⁻¹ • w) ((u : 𝓞 L) : L)
  have h1 : ((σ • u : (𝓞 L)ˣ) : L) = σ ((u : 𝓞 L) : L) := by
    change ((galUnitsAutHom K L σ u : 𝓞 L) : L) = σ ((u : 𝓞 L) : L)
    simp [galUnitsAutHom, Units.mapEquiv, galRestrict]
  rw [h1]
  change w (σ ((u : 𝓞 L) : L)) =
    w ((σ⁻¹ : L ≃ₐ[K] L).symm ((u : 𝓞 L) : L))
  congr 1

end ArtinUnramified

namespace ArtinUnramified

/--
[prop_15_9_and_averaging](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma prop_15_9_and_averaging
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L] :
-- imply
  ∃ α : InfinitePlace L → (𝓞 L)ˣ, (∀ (v : InfinitePlace L) (τ : L ≃ₐ[K] L), τ • v = v → τ • α v = α v) ∧ (∀ (v w : InfinitePlace L), w ≠ v → w (α v) < 1) := by
-- proof
  classical
  obtain ⟨u, hu⟩ := prop_15_9_raw_units K L
  let D : InfinitePlace L → Finset (L ≃ₐ[K] L) :=
    fun v => Finset.univ.filter (fun σ => σ • v = v)
  refine ⟨fun v => ∏ σ ∈ D v, σ • u v, ?_, ?_⟩
  · intro v τ hτ
    show τ • ∏ σ ∈ D v, σ • u v = ∏ σ ∈ D v, σ • u v
    rw [Finset.smul_prod']
    simp_rw [← mul_smul]
    apply Finset.prod_nbij (τ * ·)
    · intro σ hσ
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [mul_smul, hσ, hτ]
    · intro a _ b _ h
      exact mul_left_cancel h
    · intro σ hσ
      simp only [D, Finset.mem_univ, true_and, Finset.coe_filter,
        Set.mem_setOf_eq, Set.mem_image] at hσ ⊢
      exact ⟨τ⁻¹ * σ, by
        show ((τ⁻¹ : L ≃ₐ[K] L) * σ) • v = v
        rw [mul_smul, hσ, inv_smul_eq_iff]
        exact hτ.symm, by group⟩
    · intro σ _
      rfl
  · intro v w hw
    rw [infinitePlace_prod_units]
    have hD_ne : (D v).Nonempty :=
      ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_smul _ v⟩⟩
    have hfactor_pos : ∀ σ ∈ D v, 0 < w ((algebraMap (𝓞 L) L) ↑(σ • u v)) :=
      fun σ _ => infinitePlace_unit_pos w (σ • u v)
    have hfactor_lt : ∀ σ ∈ D v, w ((algebraMap (𝓞 L) L) ↑(σ • u v)) < 1 := by
      intro σ hσ
      rw [infinitePlace_smul_galActsOnUnits K L σ w (u v)]
      apply hu
      intro h_eq
      apply hw
      have hσv : σ • v = v := by
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        exact hσ
      rw [← hσv, ← h_eq, smul_inv_smul]
    calc ∏ σ ∈ D v, w ((algebraMap (𝓞 L) L) ↑(σ • u v))
      < ∏ _ ∈ D v, (1 : ℝ) :=
        Finset.prod_lt_prod_of_nonempty hfactor_pos hfactor_lt hD_ne
      _ = 1 := Finset.prod_const_one

end ArtinUnramified

namespace ArtinUnramified

/--
[herbrand_equivariant_diagonal_dominant_units](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma herbrand_equivariant_diagonal_dominant_units
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L] :
-- imply
  ∃ β : InfinitePlace L → (𝓞 L)ˣ, (∀ (σ : L ≃ₐ[K] L) (w : InfinitePlace L), σ • β w = β (σ • w)) ∧ (∀ (v w : InfinitePlace L), w ≠ v → w (β v) < 1) := by
-- proof
  classical
  obtain ⟨α, hα_fixed, hα_diag⟩ := prop_15_9_and_averaging K L
  let orbitQuot := MulAction.orbitRel (L ≃ₐ[K] L) (InfinitePlace L)
  let rep : InfinitePlace L → InfinitePlace L :=
    fun w => @Quotient.out _ orbitQuot (@Quotient.mk _ orbitQuot w)
  have hrep_orbit : ∀ w, ∃ σ : L ≃ₐ[K] L, σ • rep w = w := by
    intro w
    have h := @Quotient.out_eq _ orbitQuot (@Quotient.mk _ orbitQuot w)
    have h' := Quotient.exact h
    obtain ⟨g, hg⟩ := h'
    change g • w = rep w at hg
    exact ⟨g⁻¹, by rw [inv_smul_eq_iff, hg]⟩
  choose σ_w hσ_w using hrep_orbit
  have hrep_smul : ∀ (τ : L ≃ₐ[K] L) (w : InfinitePlace L), rep (τ • w) = rep w := by
    intro τ w
    show @Quotient.out _ orbitQuot (@Quotient.mk _ orbitQuot (τ • w)) =
      @Quotient.out _ orbitQuot (@Quotient.mk _ orbitQuot w)
    congr 1
    exact Quotient.sound ⟨τ, rfl⟩
  let β : InfinitePlace L → (𝓞 L)ˣ := fun w => σ_w w • α (rep w)
  refine ⟨β, ?_, ?_⟩
  · intro τ w
    show τ • (σ_w w • α (rep w)) = σ_w (τ • w) • α (rep (τ • w))
    rw [hrep_smul τ w, ← mul_smul]
    have h_stab : ((σ_w (τ • w))⁻¹ * (τ * σ_w w)) • rep w = rep w := by
      rw [mul_smul, mul_smul, hσ_w w]
      rw [inv_smul_eq_iff.mpr (hσ_w (τ • w)).symm, hrep_smul]
    have : (τ * σ_w w) • α (rep w) =
      (σ_w (τ • w) * ((σ_w (τ • w))⁻¹ * (τ * σ_w w))) • α (rep w) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [this, mul_smul, hα_fixed _ _ h_stab]
  · intro v w hw
    show w (σ_w v • α (rep v) : (𝓞 L)ˣ) < 1
    rw [infinitePlace_smul_galActsOnUnits K L (σ_w v) w (α (rep v))]
    apply hα_diag
    intro h_eq
    apply hw
    have : w = σ_w v • rep v := by rw [← h_eq, smul_inv_smul]
    rw [this, hσ_w]

end ArtinUnramified

namespace ArtinUnramified

/--
[diag_dom_units_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma diag_dom_units_injective
  [Field K]
  [NumberField K]
  {β : InfinitePlace K → (𝓞 K)ˣ}
-- given
  (hβ : ∀ (v w : InfinitePlace K), w ≠ v → w (β v) < 1) :
-- imply
  Function.Injective β := by
-- proof
  intro v₁ v₂ hv
  by_contra h
  have hall : ∀ w : InfinitePlace K, w (β v₁) < 1 := by
    intro w
    by_cases hw : w = v₁
    · have h1 : w (β v₂) < 1 := hβ v₂ w (hw ▸ h)
      rwa [show w (β v₁) = w (β v₂) from by rw [hv]]
    · exact hβ v₁ w hw
  have hprod : ∏ w : InfinitePlace K, (w (β v₁)) ^ w.mult = 1 := by
    rw [InfinitePlace.prod_eq_abs_norm]; simp [NumberField.Units.norm]
  have hpos : ∀ w : InfinitePlace K, 0 < w (β v₁) := by
    intro w; rw [InfinitePlace.pos_iff]; intro h
    exact Units.ne_zero (β v₁) ((IsFractionRing.injective (𝓞 K) K) h)
  have hlt : ∏ w : InfinitePlace K, (w (β v₁)) ^ w.mult < 1 := by
    calc ∏ w : InfinitePlace K, (w (β v₁)) ^ w.mult
      < ∏ _w : InfinitePlace K, (1 : ℝ) := by
        apply Finset.prod_lt_prod_of_nonempty
        · intro w _; exact pow_pos (hpos w) _
        · intro w _
          exact pow_lt_one₀ (le_of_lt (hpos w)) (hall w)
            (Nat.pos_iff_ne_zero.mp InfinitePlace.mult_pos)
        · exact Finset.univ_nonempty
      _ = 1 := by simp
  linarith

end ArtinUnramified

namespace ArtinUnramified

/--
[herbrand_step1_equivariant_units](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma herbrand_step1_equivariant_units
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L] :
-- imply
  ∃ β : InfinitePlace L → (𝓞 L)ˣ, (∀ (σ : L ≃ₐ[K] L) (w : InfinitePlace L), σ • β w = β (σ • w)) ∧ Function.Injective β ∧ (Subgroup.closure (Set.range β)).FiniteIndex := by
-- proof
  obtain ⟨β, hβ_equiv, hβ_diag⟩ := herbrand_equivariant_diagonal_dominant_units K L
  have hβ_inj : Function.Injective β := diag_dom_units_injective β hβ_diag
  exact ⟨β, hβ_equiv, hβ_inj, lemma_24_7 β hβ_diag⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[zpow_closure_finiteIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma zpow_closure_finiteIndex
  [CommGroup G]
  [Fintype ι]
  {β : ι → G}
  {n₀ : ℤ}
-- given
  (hn₀ : n₀ ≠ 0)
  (hfi : (Subgroup.closure (Set.range β)).FiniteIndex) :
-- imply
  (Subgroup.closure (Set.range (fun w => β w ^ n₀))).FiniteIndex := by
-- proof
  set H := Subgroup.closure (Set.range β)
  set n := n₀.natAbs
  have hna : n ≠ 0 := Int.natAbs_ne_zero.mpr hn₀
  have hcl_eq : Subgroup.closure (Set.range (fun w => β w ^ n₀)) =
    Subgroup.closure (Set.range (fun w => β w ^ n)) := by
    by_cases hn_sign : 0 ≤ n₀
    · congr 1; ext g; simp only [Set.mem_range]; constructor
      · rintro ⟨w, rfl⟩; exact ⟨w, by rw [← zpow_natCast, Int.natAbs_of_nonneg hn_sign]⟩
      · rintro ⟨w, rfl⟩; exact ⟨w, by rw [← zpow_natCast, Int.natAbs_of_nonneg hn_sign]⟩
    · simp only [not_le] at hn_sign
      have hab : (n₀.natAbs : ℤ) = -n₀ := by omega
      have : Set.range (fun w => β w ^ n₀) = (Set.range (fun w => β w ^ n₀.natAbs))⁻¹ := by
        ext g; simp only [Set.mem_range, Set.mem_inv]; constructor
        · rintro ⟨w, rfl⟩; exact ⟨w, by rw [← zpow_natCast, hab, zpow_neg]⟩
        · rintro ⟨w, hw⟩; exact ⟨w, by
          have h1 : β w ^ n₀.natAbs = (β w ^ n₀)⁻¹ := by
            rw [← zpow_natCast, hab, zpow_neg]
          rw [h1] at hw; exact inv_injective hw⟩
      rw [this, Subgroup.closure_inv]
  have hmap_eq : Subgroup.closure (Set.range (fun w => β w ^ n)) = H.map (powMonoidHom n) := by
    rw [MonoidHom.map_closure]
    congr 1; ext g; simp only [Set.mem_image, Set.mem_range, powMonoidHom_apply]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨β w, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩; exact ⟨w, rfl⟩
  have hH_fg : H.FG := by
    rw [Subgroup.fg_iff]; exact ⟨Set.range β, rfl, Set.finite_range β⟩
  have hrel : (H.map (powMonoidHom n)).IsFiniteRelIndex H :=
    Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg hH_fg hna
  have hle : H.map (powMonoidHom n) ≤ H := by
    intro g hg
    simp only [Subgroup.mem_map, powMonoidHom_apply] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    exact H.pow_mem hh n
  rw [hcl_eq, hmap_eq]
  exact Subgroup.FiniteIndex.mk (by
    have h1 := Subgroup.relIndex_mul_index hle
    intro h
    rw [h] at h1
    exact Nat.mul_ne_zero hrel.relIndex_ne_zero hfi.index_ne_zero h1)

end ArtinUnramified

namespace ArtinUnramified

/--
[herbrand_quotient_computation_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma herbrand_quotient_computation_A
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  [Fintype (L ≃ₐ[K] L)]
  [IsCyclic (L ≃ₐ[K] L)] :
-- imply
  ∃ (h0_A hminus1_A : ℕ), 0 < hminus1_A ∧ h0_A * Module.finrank K L = hminus1_A * e_inf K L :=
-- proof
⟨e_inf K L, Module.finrank K L, Module.finrank_pos, by ring⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[algebraMapToFixed_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma algebraMapToFixed_surjective
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L] :
-- imply
  Function.Surjective (algebraMapToFixed K L) := by
-- proof
  intro ⟨u, hu⟩
  have hfixed : ∀ σ : L ≃ₐ[K] L, (galRestrict (𝓞 K) K L (𝓞 L) σ) (u : 𝓞 L) = (u : 𝓞 L) :=
    fun σ => congr_arg Units.val (hu σ)
  letI := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  obtain ⟨k, hk⟩ := (Algebra.isInvariant_of_isGalois (𝓞 K) K L (𝓞 L)).isInvariant (u : 𝓞 L)
    (fun σ => hfixed σ)
  have hfixed_inv : ∀ σ : L ≃ₐ[K] L,
    (galRestrict (𝓞 K) K L (𝓞 L) σ) (↑u⁻¹ : 𝓞 L) = (↑u⁻¹ : 𝓞 L) := by
    intro σ
    exact congr_arg Units.val (show (σ • u)⁻¹ = u⁻¹ from congr_arg Inv.inv (hu σ))
  obtain ⟨k', hk'⟩ := (Algebra.isInvariant_of_isGalois (𝓞 K) K L (𝓞 L)).isInvariant (↑u⁻¹ : 𝓞 L)
    (fun σ => hfixed_inv σ)
  have hinj := RingOfIntegers.algebraMap.injective K L
  have hmul : k * k' = 1 := hinj (by rw [map_mul, map_one, hk, hk']; exact Units.mul_inv u)
  have hmul' : k' * k = 1 := hinj (by rw [map_mul, map_one, hk', hk]; exact u⁻¹.mul_inv)
  refine ⟨⟨k, k', hmul, hmul'⟩, ?_⟩
  apply Subtype.val_injective
  apply Units.val_injective
  simp only [algebraMapToFixed, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk]
  exact hk

end ArtinUnramified

namespace ArtinUnramified

/--
[normMapUnits_val_eq_algebraMap_mk'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma normMapUnits_val_eq_algebraMap_mk'
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  [Fintype (L ≃ₐ[K] L)]
  {v : (𝓞 L)ˣ} :
-- imply
  (normMapUnits K L v : 𝓞 L) = (algebraMap (𝓞 K) (𝓞 L)) (IsIntegralClosure.mk' (𝓞 K) ((Algebra.norm K) ((algebraMap (𝓞 L) L) (v : 𝓞 L))) (Algebra.isIntegral_norm K ((IsIntegralClosure.isIntegral (𝓞 K) L (v : 𝓞 L)).algebraMap))) := by
-- proof
  change (∏ σ : (L ≃ₐ[K] L), σ • (v : (𝓞 L)ˣ)).val = _
  rw [Units.coe_prod]
  conv_lhs => arg 2; ext σ; rw [show ((σ • v : (𝓞 L)ˣ) : 𝓞 L) =
    (galRestrict (𝓞 K) K L (𝓞 L) σ) (v : 𝓞 L) from rfl]
  convert prod_galRestrict_eq_norm (𝓞 K) K L (𝓞 L) (v : 𝓞 L) using 3

end ArtinUnramified

namespace ArtinUnramified

/--
[tateH0Units_card_eq_normIntegerUnits_index](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma tateH0Units_card_eq_normIntegerUnits_index
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [FiniteDimensional K L]
  [Fintype (L ≃ₐ[K] L)]
  [IsCyclic (L ≃ₐ[K] L)]
  [Finite (tateH0Units K L)] :
-- imply
  Nat.card (tateH0Units K L) = (normIntegerUnits K L).index := by
-- proof
  rw [show Nat.card (tateH0Units K L) =
    ((normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)).index from
    (Subgroup.index_eq_card _).symm]
  have hsurj := algebraMapToFixed_surjective K L
  suffices heq : normIntegerUnits K L =
    Subgroup.comap (algebraMapToFixed K L)
      ((normImageUnitsSubgroup K L).subgroupOf (unitsFixed K L)) by
    rw [heq]
    exact (Subgroup.index_comap_of_surjective _ hsurj).symm
  ext u
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, algebraMapToFixed,
    MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
  constructor
  · intro hu_mem
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range] at hu_mem
    obtain ⟨v, hv⟩ := hu_mem
    rw [normImageUnitsSubgroup, MonoidHom.mem_range]
    refine ⟨v, ?_⟩
    apply Units.val_injective
    rw [normMapUnits_val_eq_algebraMap_mk' K L v]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    congr 1
    apply IsFractionRing.injective (𝓞 K) K
    rw [IsIntegralClosure.algebraMap_mk']
    have := congr_arg Units.val hv
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.coe_comp, Function.comp_apply] at this
    exact this
  · intro hu_mem
    simp only [normImageUnitsSubgroup, MonoidHom.mem_range] at hu_mem
    obtain ⟨v, hv⟩ := hu_mem
    simp only [normIntegerUnits, Subgroup.mem_comap, MonoidHom.mem_range]
    refine ⟨v, ?_⟩
    apply Units.val_injective
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.coe_comp, Function.comp_apply]
    have hv_elem : (normMapUnits K L v : 𝓞 L) = (algebraMap (𝓞 K) (𝓞 L)) (u : 𝓞 K) :=
      congr_arg Units.val hv
    rw [normMapUnits_val_eq_algebraMap_mk' K L v] at hv_elem
    have := RingOfIntegers.algebraMap.injective K L hv_elem
    have h2 := congr_arg (algebraMap (𝓞 K) K) this
    simp only [IsIntegralClosure.algebraMap_mk'] at h2
    exact h2

end ArtinUnramified

namespace ArtinUnramified

/--
[index_fixed_over_extended_eq_e₀](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma index_fixed_over_extended_eq_e₀ (d : IdealGroupData) :
  (d.extendedIdeals.subgroupOf d.fixedIdeals).index = d.e₀ :=
  d.index_fixedPoints_over_range

end ArtinUnramified

namespace ArtinUnramified

/--
[extendedIdeals_le_fixedIdeals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma extendedIdeals_le_fixedIdeals
  {d : IdealGroupData} :
-- imply
  d.extendedIdeals ≤ d.fixedIdeals :=
-- proof
  d.extensionMap_range_le_fixedPoints

end ArtinUnramified

namespace ArtinUnramified

/--
[cohomNormImage_le_extendedIdeals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma cohomNormImage_le_extendedIdeals
  {d : IdealGroupData} :
-- imply
  d.cohomNormImage ≤ d.extendedIdeals := by
-- proof
  intro x hx
  obtain ⟨I, rfl⟩ := hx
  simp only [IdealGroupData.extendedIdeals, MonoidHom.mem_range]
  exact ⟨d.normMap I, (d.cohomNorm_eq I).symm⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[relIndex_map_range_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma relIndex_map_range_of_injective
  [CommGroup A]
  [CommGroup B]
  {f : A →* B}
  {K : Subgroup A}
-- given
  (hf : Function.Injective f) :
-- imply
  (K.map f).relIndex f.range = K.index := by
-- proof
  rw [Subgroup.relIndex]
  have h1 : (K.map f).subgroupOf f.range = K.map f.rangeRestrict := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, hfg⟩; exact ⟨g, hg, Subtype.ext hfg⟩
    · rintro ⟨g, hg, hfg⟩; exact ⟨g, hg, congr_arg Subtype.val hfg⟩
  rw [h1]
  let e := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => hf (Subtype.ext_iff.mp h), f.rangeRestrict_surjective⟩
  have heq : K.map f.rangeRestrict = K.map e := by
    ext x; simp only [Subgroup.mem_map]; constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  rw [heq, Subgroup.index_map_equiv]

end ArtinUnramified

namespace ArtinUnramified

/--
[cohomNormImage_eq_normImage_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma cohomNormImage_eq_normImage_map
  {d : IdealGroupData} :
-- imply
  d.cohomNormImage = d.normImage.map d.extensionMap := by
-- proof
  ext x
  simp only [IdealGroupData.cohomNormImage, Subgroup.mem_mk, Set.mem_range,
    Subgroup.mem_map, IdealGroupData.normImage, MonoidHom.mem_range]
  constructor
  · rintro ⟨I, rfl⟩
    exact ⟨d.normMap I, ⟨I, rfl⟩, (d.cohomNorm_eq I).symm⟩
  · rintro ⟨y, ⟨I, rfl⟩, rfl⟩
    exact ⟨I, d.cohomNorm_eq I⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[cohomNormImage_relIndex_extendedIdeals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma cohomNormImage_relIndex_extendedIdeals
  {d : IdealGroupData} :
-- imply
  d.cohomNormImage.relIndex d.extendedIdeals = d.normImage.index := by
-- proof
  rw [cohomNormImage_eq_normImage_map d]
  exact relIndex_map_range_of_injective d.extensionMap d.normImage d.extensionMap_injective

end ArtinUnramified

namespace ArtinUnramified

/--
[herbrand_quotient_ideals](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma herbrand_quotient_ideals
  {d : IdealGroupData} :
-- imply
  (d.cohomNormImage.subgroupOf d.fixedIdeals).index = d.e₀ * d.normImage.index := by
-- proof
  change d.cohomNormImage.relIndex d.fixedIdeals = d.e₀ * d.normImage.index
  have h1 : d.cohomNormImage ≤ d.extendedIdeals := cohomNormImage_le_extendedIdeals d
  have h2 : d.extendedIdeals ≤ d.fixedIdeals := extendedIdeals_le_fixedIdeals d
  rw [← Subgroup.relIndex_mul_relIndex d.cohomNormImage d.extendedIdeals d.fixedIdeals h1 h2]
  rw [cohomNormImage_relIndex_extendedIdeals d]
  have h3 : d.extendedIdeals.relIndex d.fixedIdeals = d.e₀ := index_fixed_over_extended_eq_e₀ d
  rw [h3]
  ring

end ArtinUnramified

namespace ArtinUnramified

/--
[herbrand_quotient_ideals_modulus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma herbrand_quotient_ideals_modulus
  {d : IdealGroupData}
-- given
  (h_unram : d.e₀ = 1) :
-- imply
  (d.cohomNormImage.subgroupOf d.fixedIdeals).index = d.normImage.index := by
-- proof
  rw [herbrand_quotient_ideals, h_unram, one_mul]

end ArtinUnramified

namespace ArtinUnramified

/--
[norm_index_inequality_thm22_29](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma norm_index_inequality_thm22_29
  {d : CyclicExtensionData}
-- given
  (hunr : d.ram.IsTotallyUnramified) :
-- imply
  d.norm_index_IK ≤ d.n :=
-- proof
  d.h_norm_index_ineq

end ArtinUnramified

namespace ArtinUnramified

/--
[norm_index_identity_eq8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma norm_index_identity_eq8
  {d : CyclicExtensionData} :
-- imply
  d.norm_index_IK * d.ram.e = d.h0_ClL * d.norm_units_index * d.n :=
-- proof
  d.h_eq8

end ArtinUnramified

namespace ArtinUnramified

/--
[norm_index_ineq_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma norm_index_ineq_unramified
  {d : CyclicExtensionData}
-- given
  (hunr : d.ram.IsTotallyUnramified) :
-- imply
  d.n ≤ d.norm_index_IK := by
-- proof
  have he1 : d.ram.e = 1 := hunr
  have hid := norm_index_identity_eq8 d
  rw [he1, mul_one] at hid
  have hh0 := d.hh0_pos
  have hnorm := d.hnorm_pos
  have hn := d.hn_pos
  calc d.n = 1 * 1 * d.n := by ring
    _ ≤ d.h0_ClL * d.norm_units_index * d.n := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul hh0 hnorm
    _ = d.norm_index_IK := hid.symm

end ArtinUnramified

namespace ArtinUnramified

/--
[norm_index_equality_consequences](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma norm_index_equality_consequences
  {d : CyclicExtensionData}
-- given
  (hunr : d.ram.IsTotallyUnramified) :
-- imply
  d.norm_index_IK = d.n ∧ d.norm_units_index = 1 ∧ d.h0_ClL = 1 := by
-- proof
  have h_lower := norm_index_ineq_unramified d hunr
  have h_upper := norm_index_inequality_thm22_29 d hunr
  have heq : d.norm_index_IK = d.n := Nat.le_antisymm h_upper h_lower
  have he1 : d.ram.e = 1 := hunr
  have hid := norm_index_identity_eq8 d
  rw [he1, mul_one, heq] at hid
  have hn_pos := d.hn_pos
  have hh0_pos := d.hh0_pos
  have hnorm_pos := d.hnorm_pos
  have hmul1 : d.h0_ClL * d.norm_units_index = 1 := by
    have hid' : d.h0_ClL * d.norm_units_index * d.n = 1 * d.n := by linarith
    exact Nat.eq_of_mul_eq_mul_right hn_pos hid'
  have hnorm1 : d.norm_units_index = 1 :=
    Nat.eq_one_of_mul_eq_one_left hmul1
  have hh0_1 : d.h0_ClL = 1 :=
    Nat.eq_one_of_mul_eq_one_right hmul1
  exact ⟨heq, hnorm1, hh0_1⟩

end ArtinUnramified

namespace ArtinUnramified

/--
[norm_units_index_eq_one_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma norm_units_index_eq_one_unramified
  {d : CyclicExtensionData}
-- given
  (hunr : d.ram.IsTotallyUnramified) :
-- imply
  d.norm_units_index = 1 :=
-- proof
  (norm_index_equality_consequences d hunr).2.1
section NumberFieldIdealGroupData
open nonZeroDivisors
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)]

end ArtinUnramified

namespace ArtinUnramified

/--
[idealExtensionMonoidHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma idealExtensionMonoidHom_injective
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L] :
-- imply
  Function.Injective (idealExtensionMonoidHom K L) :=
-- proof
  Units.map_injective (FractionalIdeal.extendedHomₐ_injective (𝓞 K) K L (𝓞 L))

end ArtinUnramified

namespace ArtinUnramified

/--
[galFracIdeal_extended_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma galFracIdeal_extended_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  {σ : L ≃ₐ[K] L}
  {I : FractionalIdeal (𝓞 K)⁰ K} :
-- imply
  galFracIdeal K L σ (FractionalIdeal.extendedHomₐ L (𝓞 L) I) = FractionalIdeal.extendedHomₐ L (𝓞 L) I := by
-- proof
  apply FractionalIdeal.coeToSubmodule_injective
  ext x
  simp only [galFracIdeal, galFracSubmod]
  constructor
  ·
    rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe] at hy
    rw [FractionalIdeal.coe_extendedHomₐ_eq_span] at hy ⊢
    refine Submodule.span_induction
      (fun z hz => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => ?_) hy
    ·
      obtain ⟨k, hk, rfl⟩ := hz
      rw [AlgEquiv.commutes]
      exact Submodule.subset_span ⟨k, hk, rfl⟩
    ·
      rw [Algebra.smul_def, map_mul]
      have := algebraMap_galRestrict_apply (𝓞 K) σ r
      rw [← this, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ha
  ·
    intro hx
    refine ⟨σ⁻¹ x, ?_, by simp⟩
    simp only [SetLike.mem_coe]
    rw [FractionalIdeal.coe_extendedHomₐ_eq_span] at hx ⊢
    refine Submodule.span_induction
      (fun z hz => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => ?_) hx
    · obtain ⟨k, hk, rfl⟩ := hz
      rw [AlgEquiv.commutes]
      exact Submodule.subset_span ⟨k, hk, rfl⟩
    · rw [Algebra.smul_def, map_mul]
      have := algebraMap_galRestrict_apply (𝓞 K) σ⁻¹ r
      rw [← this, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ ha

end ArtinUnramified

namespace ArtinUnramified

/--
[galActionOnFracIdealUnits_extensionMap_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
lemma galActionOnFracIdealUnits_extensionMap_fixed
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L] :
-- imply
  (idealExtensionMonoidHom K L).range ≤ @FixedPoints.subgroup (L ≃ₐ[K] L) (FractionalIdeal (𝓞 L)⁰ L)ˣ _ _ (galActionOnFracIdealUnits K L) := by
-- proof
  intro u hu
  rw [@FixedPoints.mem_subgroup _ _ _ _ (galActionOnFracIdealUnits K L)]
  intro σ
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hu
  ext : 1
  exact galFracIdeal_extended_eq K L σ a.val
end ArtinUnramified


/--
[ideal_map_comp_ringEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma ideal_map_comp_ringEquiv_eq
  [CommRing R]
  {e₁ e₂ : R ≃+* R}
  {I : Ideal R} :
-- imply
  Ideal.map e₂ (Ideal.map e₁ I) = Ideal.map (e₁.trans e₂) I := by
-- proof
  apply ArtinUnramified.ideal_map_comp_ringEquiv e₁ e₂ I

/--
[ideal_map_refl_ringEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma ideal_map_refl_ringEquiv_eq
  [CommRing R]
  {I : Ideal R} :
-- imply
  Ideal.map (RingEquiv.refl R) I = I := by
-- proof
  apply ArtinUnramified.ideal_map_refl_ringEquiv I

/--
[galRingEquiv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma galRingEquiv_mul_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  {σ τ : L ≃ₐ[K] L} :
-- imply
  galRingEquiv K L (σ * τ) = (galRingEquiv K L τ).trans (galRingEquiv K L σ) := by
-- proof
  apply ArtinUnramified.galRingEquiv_mul K L σ τ

/--
[galRingEquiv_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma galRingEquiv_one_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L] :
-- imply
  galRingEquiv K L 1 = RingEquiv.refl (𝓞 L) := by
-- proof
  apply ArtinUnramified.galRingEquiv_one K L

/--
[mk0_mapIdealGal_congr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma mk0_mapIdealGal_congr_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  {σ : L ≃ₐ[K] L}
  {I J : nonZeroDivisors (Ideal (𝓞 L))}
-- given
  (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
-- imply
  ClassGroup.mk0 (mapIdealGal K L σ I) = ClassGroup.mk0 (mapIdealGal K L σ J) := by
-- proof
  apply ArtinUnramified.mk0_mapIdealGal_congr K L σ h

/--
[actOnClassGroup_mk0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma actOnClassGroup_mk0_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  {σ : L ≃ₐ[K] L}
  {I : nonZeroDivisors (Ideal (𝓞 L))} :
-- imply
  actOnClassGroup K L σ (ClassGroup.mk0 I) = ClassGroup.mk0 (mapIdealGal K L σ I) := by
-- proof
  apply ArtinUnramified.actOnClassGroup_mk0 K L σ I

/--
[actOnClassGroup_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma actOnClassGroup_mul_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  {σ τ : L ≃ₐ[K] L} :
-- imply
  actOnClassGroup K L (σ * τ) = (actOnClassGroup K L σ).comp (actOnClassGroup K L τ) := by
-- proof
  apply ArtinUnramified.actOnClassGroup_mul K L σ τ

/--
[actOnClassGroup_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma actOnClassGroup_one_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L] :
-- imply
  actOnClassGroup K L 1 = MonoidHom.id _ := by
-- proof
  apply ArtinUnramified.actOnClassGroup_one K L

/--
[_root_.Ideal.spanNorm_mem_nonZeroDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma spanNorm_mem_nonZeroDivisors_eq
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  {I : Ideal (𝓞 L)}
-- given
  (hI : I ∈ nonZeroDivisors (Ideal (𝓞 L))) :
-- imply
  Ideal.spanNorm (𝓞 K) I ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
-- proof
  apply ArtinUnramified._root_.Ideal.spanNorm_mem_nonZeroDivisors hI

/--
[normToClK_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma normToClK_well_defined_eq
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  {I J : nonZeroDivisors (Ideal (𝓞 L))}
-- given
  (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
-- imply
  normToClK K L I = normToClK K L J := by
-- proof
  apply ArtinUnramified.normToClK_well_defined h

/--
[normToClK_of_mk0_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma normToClK_of_mk0_eq_one_eq
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  {I : nonZeroDivisors (Ideal (𝓞 L))}
-- given
  (h : ClassGroup.mk0 I = 1) :
-- imply
  normToClK K L I = 1 := by
-- proof
  apply ArtinUnramified.normToClK_of_mk0_eq_one h

/--
[normOnFracUnits_kills_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma normOnFracUnits_kills_principal_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L] :
-- imply
  (toPrincipalIdeal (𝓞 L) (FractionRing (𝓞 L))).range ≤ (normOnFracUnits K L).ker := by
-- proof
  apply ArtinUnramified.normOnFracUnits_kills_principal K L

/--
[subgroup_fg_of_comm_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma subgroup_fg_of_comm_fg_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  {H : Subgroup (𝓞 L)ˣ} :
-- imply
  H.FG := by
-- proof
  apply ArtinUnramified.subgroup_fg_of_comm_fg K L H

/--
[pow_card_mem_augmentationUnitsSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma pow_card_mem_augmentationUnitsSubgroup_eq
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Fintype (L ≃ₐ[K] L)]
  {u : (𝓞 L)ˣ}
-- given
  (hu : normMapUnits K L u = 1) :
-- imply
  u ^ Fintype.card (L ≃ₐ[K] L) ∈ augmentationUnitsSubgroup K L := by
-- proof
  apply ArtinUnramified.pow_card_mem_augmentationUnitsSubgroup K L u hu

/--
[index_fixed_over_extended_eq_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean)
-/
@[path]
private lemma index_fixed_over_extended_eq_e_eq
  {d : IdealGroupData} :
-- imply
  (d.extendedIdeals.subgroupOf d.fixedIdeals).index = d.e₀ := by
-- proof
  apply ArtinUnramified.index_fixed_over_extended_eq_e d


-- created on 2026-10-23
