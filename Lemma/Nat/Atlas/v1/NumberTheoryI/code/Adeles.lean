import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
open NumberField IsDedekindDomain NumberField.Adeles
open scoped TensorProduct
open Filter Set Topology
open NumberField.InfiniteAdeleRing NumberField.InfinitePlace.Completion NumberField.mixedEmbedding NumberField.InfinitePlace in


namespace NumberField.Adeles

/--
[placeNorm_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma placeNorm_mul
  [Field K]
  [NumberField K]
  {v : Place K}
  {x y : K} :
-- imply
  placeNorm v (x * y) = placeNorm v x * placeNorm v y := by
-- proof
  match v with
  | .finite vi => exact map_mul (NumberField.HeightOneSpectrum.adicAbv K vi) x y
  | .infinite w => exact w.1.map_mul x y

end NumberField.Adeles

namespace NumberField.Adeles

/--
[placeNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma placeNorm_nonneg
  [Field K]
  [NumberField K]
  {v : Place K}
  {x : K} :
-- imply
  0 ≤ placeNorm v x := by
-- proof
  match v with
  | .finite vi => exact (NumberField.HeightOneSpectrum.adicAbv K vi).nonneg x
  | .infinite w => exact w.1.nonneg x

end NumberField.Adeles

namespace NumberField.Adeles

/--
[placeNorm_eq_placeNormAdele_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma placeNorm_eq_placeNormAdele_algebraMap
  [Field K]
  [NumberField K]
  {v : Place K}
  {x : K} :
-- imply
  placeNorm v x = placeNormAdele v (algebraMap K (adeleRing (K := K)) x) := by
-- proof
  match v with
  | .infinite w =>
    show w x = ‖(algebraMap K (InfiniteAdeleRing K) x) w‖
    rw [show (algebraMap K (InfiniteAdeleRing K) x) w = algebraMap K w.Completion x from rfl]
    rw [show algebraMap K w.Completion x =
      (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe]
    simp
  | .finite vi =>
    show NumberField.HeightOneSpectrum.adicAbv K vi x =
      ‖(algebraMap K (adeleRing (K := K)) x).2 vi‖
    rw [show (algebraMap K (adeleRing (K := K)) x).2 vi =
      algebraMap K (vi.adicCompletion K) x from rfl]
    rw [show algebraMap K (vi.adicCompletion K) x = FinitePlace.embedding vi x from rfl]
    rw [FinitePlace.norm_embedding]

end NumberField.Adeles

namespace NumberField.Adeles

/--
[restrictedProduct_topology_eq_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma restrictedProduct_topology_eq_iSup
  [Field K]
  [NumberField K]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  [∀ i, TopologicalSpace (X i)]
  {𝓕 : Filter ι} :
-- imply
  RestrictedProduct.topologicalSpace X U 𝓕 = ⨆ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), TopologicalSpace.coinduced (RestrictedProduct.inclusion X U hS) (RestrictedProduct.topologicalSpace X U (𝓟 S)) :=
-- proof
  RestrictedProduct.topologicalSpace_eq_iSup 𝓕

end NumberField.Adeles

namespace NumberField.Adeles

/--
[restrictedProduct_inclusion_isEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma restrictedProduct_inclusion_isEmbedding
  [Field K]
  [NumberField K]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  [∀ i, TopologicalSpace (X i)]
  {𝓕 : Filter ι}
  {S : Set ι}
-- given
  (hS : 𝓕 ≤ 𝓟 S) :
-- imply
  Topology.IsEmbedding (RestrictedProduct.inclusion X U hS) :=
-- proof
  RestrictedProduct.isEmbedding_inclusion_principal hS

end NumberField.Adeles

namespace NumberField.Adeles

/--
[restrictedProduct_inclusion_isOpenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma restrictedProduct_inclusion_isOpenEmbedding
  [Field K]
  [NumberField K]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  [∀ i, TopologicalSpace (X i)]
  {S : Set ι}
-- given
  (hU_open : ∀ i, IsOpen (U i))
  (hS : cofinite ≤ 𝓟 S) :
-- imply
  Topology.IsOpenEmbedding (RestrictedProduct.inclusion X U hS) :=
-- proof
  RestrictedProduct.isOpenEmbedding_inclusion_principal hU_open hS

end NumberField.Adeles

namespace NumberField.Adeles

/--
[restrictedProduct_continuous_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma restrictedProduct_continuous_iff
  [Field K]
  [NumberField K]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  [∀ i, TopologicalSpace (X i)]
  {𝓕 : Filter ι}
  [TopologicalSpace Y]
  {f : (Πʳ i, [X i, U i]_[𝓕]) → Y} :
-- imply
  Continuous f ↔ ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S), Continuous (f ∘ RestrictedProduct.inclusion X U hS) :=
-- proof
  RestrictedProduct.continuous_dom

end NumberField.Adeles

namespace NumberField.Adeles

/--
[finiteAdeleRing_topology_eq_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma finiteAdeleRing_topology_eq_iSup
  [Field K]
  [NumberField K] :
-- imply
  RestrictedProduct.topologicalSpace (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) cofinite = ⨆ (S : Set (HeightOneSpectrum (𝓞 K))) (hS : cofinite ≤ 𝓟 S), TopologicalSpace.coinduced (RestrictedProduct.inclusion (fun v => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) hS) (RestrictedProduct.topologicalSpace (fun v => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) (𝓟 S)) :=
-- proof
  RestrictedProduct.topologicalSpace_eq_iSup cofinite

end NumberField.Adeles

namespace NumberField.Adeles

/--
[finiteAdeleRing_inclusion_isOpenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma finiteAdeleRing_inclusion_isOpenEmbedding
  [Field K]
  [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
-- given
  (hS : cofinite ≤ 𝓟 S) :
-- imply
  Topology.IsOpenEmbedding (RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) hS) :=
-- proof
  RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1) hS

end NumberField.Adeles

namespace NumberField.Adeles

/--
[diag_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma diag_injective
  [Field K]
  [NumberField K] :
-- imply
  Function.Injective (algebraMap K (adeleRing (K := K))) :=
-- proof
  AdeleRing.algebraMap_injective (𝓞 K) K

end NumberField.Adeles

namespace NumberField.Adeles

/--
[eq_zero_of_integral_and_inf_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma eq_zero_of_integral_and_inf_lt_one
  [Field K]
  [NumberField K]
  {k : 𝓞 K}
-- given
  (hinf : ∀ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) < 1) :
-- imply
  k = 0 := by
-- proof
  suffices h : (algebraMap (𝓞 K) K) k = 0 from Subtype.coe_injective h
  by_contra hk
  have h_prod_lt : ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) ^ w.mult < 1 := by
    classical
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    rw [(Finset.mul_prod_erase Finset.univ
      (fun w : InfinitePlace K => w (algebraMap (𝓞 K) K k) ^ w.mult)
      (Finset.mem_univ w₀)).symm]
    calc _ ≤ (w₀ (algebraMap (𝓞 K) K k) ^ w₀.mult) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_one
        · intro w _; exact pow_nonneg (w.1.nonneg _) _
        · intro w _; exact pow_le_one₀ (w.1.nonneg _) (le_of_lt (hinf w))
      · exact le_of_lt (pow_pos (w₀.1.pos hk) _)
      _ = w₀ (algebraMap (𝓞 K) K k) ^ w₀.mult := mul_one _
      _ < 1 := pow_lt_one₀ (w₀.1.nonneg _) (hinf w₀) w₀.mult_pos.ne'
  have h_prod := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K k)
  have h_norm_loc : (Algebra.norm ℚ) ((algebraMap (𝓞 K) K) k) =
    algebraMap ℤ ℚ ((Algebra.norm ℤ) k) :=
    Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ) k
  rw [h_norm_loc] at h_prod; rw [h_prod] at h_prod_lt
  have h_norm_zero : (Algebra.norm ℤ) k = 0 := by
    by_contra hn
    have h1 : |(((Algebra.norm ℤ) k : ℤ) : ℝ)| < 1 := by
      have : ((Algebra.norm ℤ k : ℤ) : ℝ) =
        ((algebraMap ℤ ℚ ((Algebra.norm ℤ) k) : ℚ) : ℝ) := rfl
      rw [this]; exact_mod_cast h_prod_lt
    have h2 := abs_lt.mp h1
    have h3 : (-1 : ℤ) < (Algebra.norm ℤ) k := by exact_mod_cast h2.1
    have h4 : ((Algebra.norm ℤ) k : ℤ) < 1 := by exact_mod_cast h2.2
    omega
  rw [Algebra.norm_eq_zero_iff] at h_norm_zero
  exact hk (by simp [h_norm_zero])

end NumberField.Adeles

namespace NumberField.Adeles

/--
[mem_ringOfIntegers_of_finiteAdele_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma mem_ringOfIntegers_of_finiteAdele_integral
  [Field K]
  [NumberField K]
  {x : K}
-- given
  (h : algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite)) :
-- imply
  x ∈ (algebraMap (𝓞 K) K).range := by
-- proof
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one K x
  intro v
  obtain ⟨a, ha⟩ := h
  suffices Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1 by
    rwa [show Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x from by
      rw [v.valuedAdicCompletion_def K]
      show Valued.extensionValuation ((x : v.adicCompletion K)) = _
      rw [Valued.extensionValuation_apply_coe]; rfl] at this
  change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) x).val v) ≤ 1
  rw [show (algebraMap K (FiniteAdeleRing (𝓞 K) K) x).val v =
    (RestrictedProduct.structureMap _ _ _ a).val v from
    congr_arg (fun y => y.val v) ha.symm]
  exact (a v).prop

end NumberField.Adeles

namespace NumberField.Adeles

/--
[principalAdeles_discrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma principalAdeles_discrete
  [Field K]
  [NumberField K] :
-- imply
  DiscreteTopology (principalSubgroup (K := K)) := by
-- proof
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  let U_inf := {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1}
  let U_fin := Set.range (RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite)
  refine ⟨U_inf ×ˢ U_fin, ?_, ?_⟩
  ·
    apply IsOpen.prod
    ·
      change IsOpen {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1}
      have : {f : InfiniteAdeleRing K | ∀ w, ‖f w‖ < 1} =
        ⋂ w, {f : InfiniteAdeleRing K | ‖f w‖ < 1} := by
        ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this]
      exact isOpen_iInter_of_finite (fun w =>
        isOpen_lt (continuous_norm.comp (continuous_apply w)) continuous_const)
    ·
      exact (RestrictedProduct.isOpenEmbedding_structureMap
        (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1)).isOpen_range
  ·
    ext ⟨a, ha⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, AddSubgroup.mk_eq_zero]
    constructor
    ·
      intro ⟨h_inf, h_fin⟩
      obtain ⟨x, hx⟩ := ha
      have hx_int : x ∈ (algebraMap (𝓞 K) K).range := by
        apply mem_ringOfIntegers_of_finiteAdele_integral
        rwa [show algebraMap K (FiniteAdeleRing (𝓞 K) K) x = a.2 from by rw [← hx]; rfl]
      obtain ⟨k, hk⟩ := hx_int
      have hinf : ∀ w : InfinitePlace K, w (algebraMap (𝓞 K) K k) < 1 := by
        intro w
        have hw := h_inf w
        rw [hk]
        have ha1 : a.1 = algebraMap K (InfiniteAdeleRing K) x := by rw [← hx]; rfl
        rw [ha1] at hw
        rw [show (algebraMap K (InfiniteAdeleRing K) x w : w.Completion) =
          algebraMap K w.Completion x from rfl] at hw
        rwa [show ‖algebraMap K w.Completion x‖ = w x from by
          rw [show algebraMap K w.Completion x =
            (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
          rw [InfinitePlace.Completion.norm_coe]; simp] at hw
      have hk0 := eq_zero_of_integral_and_inf_lt_one k hinf
      rw [← hx, ← hk, hk0, map_zero, map_zero]
    ·
      intro h0; subst h0
      exact ⟨fun w => by show ‖(0 : w.Completion)‖ < 1; rw [norm_zero]; exact one_pos,
        ⟨0, by ext v; rfl⟩⟩

end NumberField.Adeles

namespace NumberField.Adeles

/--
[isCompact_finiteAdeleRing_integralSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma isCompact_finiteAdeleRing_integralSet
  [Field K]
  [NumberField K] :
-- imply
  IsCompact {a : FiniteAdeleRing (𝓞 K) K | ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} := by
-- proof
  have heq : {a : FiniteAdeleRing (𝓞 K) K |
    ∀ v : HeightOneSpectrum (𝓞 K),
      a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} =
    Set.range (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K))
      Filter.cofinite) := by
    rw [RestrictedProduct.range_structureMap]
    ext a; simp only [Set.mem_setOf_eq]
    exact ⟨fun h v => h v, fun h v => h v⟩
  rw [heq]
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
    CompactSpace ↑(v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v; change CompactSpace (Valued.integer (v.adicCompletion K)); infer_instance
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adeles_integral_set_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adeles_integral_set_compact
  [Field K]
  [NumberField K] :
-- imply
  IsCompact ((Set.pi Set.univ (fun (v : InfinitePlace K) => Metric.closedBall (0 : v.Completion) 1)) ×ˢ {a : FiniteAdeleRing (𝓞 K) K | ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}) := by
-- proof
  apply IsCompact.prod
  · exact isCompact_univ_pi (fun v => isCompact_closedBall 0 1)
  · exact isCompact_finiteAdeleRing_integralSet

end NumberField.Adeles

namespace NumberField.Adeles

/--
[valued_algebraMap_eq_valuation_crt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma valued_algebraMap_eq_valuation_crt
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {x : K} :
-- imply
  Valued.v (algebraMap K (v.adicCompletion K) x) = (v.valuation K) x := by
-- proof
  rw [show algebraMap K (v.adicCompletion K) x =
    ↑((WithVal.equiv (v.valuation K)).symm x) from rfl]
  exact v.valuedAdicCompletion_eq_valuation' x

end NumberField.Adeles

namespace NumberField.Adeles

/--
[algebraMap_div_mem_adicCompletionIntegers_crt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma algebraMap_div_mem_adicCompletionIntegers_crt
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {r d : 𝓞 K}
-- given
  (h : v.intValuation r ≤ v.intValuation d) :
-- imply
  algebraMap K (v.adicCompletion K) ((r : K) / (d : K)) ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
-- proof
  show Valued.v (algebraMap K (v.adicCompletion K) ((r : K) / (d : K))) ≤ 1
  rw [valued_algebraMap_eq_valuation_crt, map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact div_le_one_of_le₀ h (WithZero.zero_le _)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[intValuation_le_exp_of_mem_pow_crt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma intValuation_le_exp_of_mem_pow_crt
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {r : 𝓞 K}
  {n : ℕ}
-- given
  (hr : r ∈ v.asIdeal ^ n) :
-- imply
  v.intValuation r ≤ WithZero.exp (-↑n) := by
-- proof
  rw [v.intValuation_le_pow_iff_dvd]
  rwa [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]

end NumberField.Adeles

namespace NumberField.Adeles

/--
[intValuation_le_of_mem_pow_ge_crt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma intValuation_le_of_mem_pow_ge_crt
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {r d : 𝓞 K}
  {n : ℕ}
-- given
  (hd : d ≠ 0)
  (hn : ((-WithZero.log (v.intValuation d)).toNat) ≤ n)
  (hr : r ∈ v.asIdeal ^ n) :
-- imply
  v.intValuation r ≤ v.intValuation d := by
-- proof
  have hne := HeightOneSpectrum.intValuation_ne_zero v d hd
  have hle : WithZero.log (v.intValuation d) ≤ 0 := by
    have h1 := v.intValuation_le_one d
    rw [← WithZero.exp_log hne] at h1
    rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  calc v.intValuation r
    ≤ WithZero.exp (-↑n) := intValuation_le_exp_of_mem_pow_crt v r n hr
    _ ≤ WithZero.exp (-↑((-WithZero.log (v.intValuation d)).toNat)) := by
      rw [WithZero.exp_le_exp]; omega
    _ = v.intValuation d := by
      conv_rhs => rw [← WithZero.exp_log hne]
      congr 1; rw [Int.toNat_of_nonneg (neg_nonneg.mpr hle), neg_neg]

end NumberField.Adeles

namespace NumberField.Adeles

/--
[exists_integral_approx_at_place](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma exists_integral_approx_at_place
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {x : v.adicCompletion K} :
-- imply
  ∃ c : K, (x - algebraMap K (v.adicCompletion K) c) ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
-- proof
  set U := (fun y => x - y) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hU_open : IsOpen U :=
    (continuous_const.sub continuous_id).isOpen_preimage _ (Valued.isOpen_valuationSubring _)
  have hU_ne : U.Nonempty :=
    ⟨x, show x - x ∈ (v.adicCompletionIntegers K : Set _) by
      rw [sub_self]; exact (v.adicCompletionIntegers K).zero_mem⟩
  obtain ⟨c, hc⟩ := (v.denseRange_algebraMap K).exists_mem_open hU_open hU_ne
  exact ⟨c, hc⟩

end NumberField.Adeles

namespace NumberField.Adeles

/--
[crt_finite_places_covering](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma crt_finite_places_covering
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {a : FiniteAdeleRing (𝓞 K) K} :
-- imply
  ∃ c : K, ∀ v : HeightOneSpectrum (𝓞 K), (a v - algebraMap K (v.adicCompletion K) c) ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
-- proof
  classical
  have ha := a.property
  rw [Filter.eventually_cofinite] at ha
  let S := ha.toFinset
  have hdense : ∀ v : HeightOneSpectrum (𝓞 K), ∃ c : K,
    (a v - algebraMap K (v.adicCompletion K) c) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => exists_integral_approx_at_place v (a v)
  choose c_all hc_all using hdense
  obtain ⟨⟨d, hd_mem⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (S.image c_all)
  have hd_ne : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero hd_mem
  have hd_K_ne : ((d : 𝓞 K) : K) ≠ 0 := by exact_mod_cast hd_ne
  have hn_exists : ∀ v ∈ S, ∃ n : 𝓞 K,
    algebraMap (𝓞 K) K n = (d : 𝓞 K) • c_all v :=
    fun v hv => hd _ (Finset.mem_image_of_mem _ hv)
  let e : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => (-WithZero.log (v.intValuation d)).toNat
  have hT_finite : Set.Finite {v : HeightOneSpectrum (𝓞 K) | d ∈ v.asIdeal} := by
    have hI : Ideal.span ({d} : Set (𝓞 K)) ≠ 0 := by simp [hd_ne]
    exact (Ideal.finite_factors hI).subset
      (fun v hv => Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv)))
  let T := hT_finite.toFinset \ S
  let ST := S ∪ T
  let hn_exists' : ∀ v ∈ S, 𝓞 K := fun v hv => (hn_exists v hv).choose
  have hn_spec : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S),
    algebraMap (𝓞 K) K (hn_exists' v hv) = (d : 𝓞 K) • c_all v :=
    fun v hv => (hn_exists v hv).choose_spec
  let target : {v // v ∈ ST} → 𝓞 K := fun ⟨v, hv⟩ =>
    if h : v ∈ S then hn_exists' v h else 0
  have hprime : ∀ i ∈ ST, Prime ((id i : HeightOneSpectrum (𝓞 K)).asIdeal) :=
    fun i _ => i.prime
  have hcoprime : ∀ i ∈ ST, ∀ j ∈ ST, i ≠ j →
    (id i : HeightOneSpectrum (𝓞 K)).asIdeal ≠ (id j).asIdeal :=
    fun _ _ _ _ h heq => h (HeightOneSpectrum.ext heq)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) e hprime hcoprime target
  refine ⟨(y : K) / (d : K), fun v => ?_⟩
  by_cases hv_in_S : v ∈ S
  ·
    have hv_ST : v ∈ ST := Finset.mem_union_left T hv_in_S
    have hy_v := hy v hv_ST
    have htarget : target ⟨v, hv_ST⟩ = hn_exists' v hv_in_S := dif_pos hv_in_S
    rw [htarget] at hy_v
    have hmem_neg : hn_exists' v hv_in_S - y ∈ v.asIdeal ^ e v := by
      rw [show hn_exists' v hv_in_S - y = -(y - hn_exists' v hv_in_S) from by ring]
      exact neg_mem hy_v
    have hval_le : v.intValuation (hn_exists' v hv_in_S - y) ≤ v.intValuation d :=
      intValuation_le_of_mem_pow_ge_crt v (hn_exists' v hv_in_S - y) d hd_ne (e v) le_rfl hmem_neg
    have hdiv_mem : algebraMap K (v.adicCompletion K)
      ((hn_exists' v hv_in_S - y : 𝓞 K) / (d : K)) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      algebraMap_div_mem_adicCompletionIntegers_crt v _ d hval_le
    have hc_v_eq : c_all v = (hn_exists' v hv_in_S : K) / (d : K) := by
      have := hn_spec v hv_in_S
      rw [Algebra.smul_def] at this
      rwa [eq_div_iff hd_K_ne, mul_comm]
    rw [show (y : K) / (d : K) = c_all v + ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K) from by
      rw [hc_v_eq]; field_simp; ring]
    rw [show a v - algebraMap K (v.adicCompletion K)
      (c_all v + ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K)) =
      (a v - algebraMap K (v.adicCompletion K) (c_all v)) -
        algebraMap K (v.adicCompletion K) (((y : K) - (hn_exists' v hv_in_S : K)) / (d : K)) from by
      simp only [map_add]; ring]
    apply sub_mem (hc_all v)
    rw [show ((y : K) - (hn_exists' v hv_in_S : K)) / (d : K) =
      -((hn_exists' v hv_in_S : K) - (y : K)) / (d : K) from by ring]
    rw [neg_div]
    rw [map_neg]
    exact neg_mem hdiv_mem
  ·
    have hav : a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      by_contra h
      exact hv_in_S (ha.mem_toFinset.mpr h)
    suffices h_yd : algebraMap K (v.adicCompletion K) ((y : K) / (d : K)) ∈
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) from by
      have := sub_mem hav h_yd
      convert this using 1
    by_cases hv_d : d ∈ v.asIdeal
    ·
      have hv_T : v ∈ T := by
        simp only [T, Finset.mem_sdiff]
        exact ⟨hT_finite.mem_toFinset.mpr hv_d, hv_in_S⟩
      have hv_ST : v ∈ ST := Finset.mem_union_right S hv_T
      have hy_v := hy v hv_ST
      have htarget : target ⟨v, hv_ST⟩ = 0 := dif_neg hv_in_S
      rw [htarget] at hy_v
      simp only [sub_zero] at hy_v
      exact algebraMap_div_mem_adicCompletionIntegers_crt v y d
        (intValuation_le_of_mem_pow_ge_crt v y d hd_ne (e v) le_rfl hy_v)
    ·
      have hval_d : v.intValuation d = 1 :=
        HeightOneSpectrum.intValuation_eq_one_iff.mpr hv_d
      exact algebraMap_div_mem_adicCompletionIntegers_crt v y d
        (by rw [hval_d]; exact v.intValuation_le_one y)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[one_le_coveringBound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma one_le_coveringBound
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  1 ≤ coveringBound K :=
-- proof
  le_max_left 1 _

end NumberField.Adeles

namespace NumberField.Adeles

/--
[coveringBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma coveringBound_pos
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  0 < coveringBound K :=
-- proof
  lt_of_lt_of_le one_pos (one_le_coveringBound K)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[coveringBound_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma coveringBound_ne_zero
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  coveringBound K ≠ 0 :=
-- proof
  ne_of_gt (coveringBound_pos K)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[coveringBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma coveringBound_nonneg
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  0 ≤ coveringBound K :=
-- proof
  le_of_lt (coveringBound_pos K)
open scoped Classical in
open NumberField.InfiniteAdeleRing NumberField.InfinitePlace.Completion
  NumberField.mixedEmbedding NumberField.InfinitePlace in

end NumberField.Adeles

namespace NumberField.Adeles

/--
[lattice_covering_infinite_places](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma lattice_covering_infinite_places
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {f : InfiniteAdeleRing K}
  {c₁ : K} :
-- imply
  ∃ r : 𝓞 K, ∀ w : InfinitePlace K, ‖f w - algebraMap K w.Completion (c₁ + algebraMap (𝓞 K) K r)‖ ≤ coveringBound K := by
-- proof
  set g := ringEquiv_mixedSpace K (f - algebraMap K _ c₁) with hg_def
  set fl := ZSpan.floor (latticeBasis K) g
  have fl_mem : (fl : mixedSpace K) ∈
    Submodule.span ℤ (Set.range (latticeBasis K)) := fl.property
  rw [mem_span_latticeBasis] at fl_mem
  change (fl : mixedSpace K) ∈
    ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap.range at fl_mem
  obtain ⟨r, hr⟩ := fl_mem
  have hr' : mixedEmbedding K (algebraMap (𝓞 K) K r) = (fl : mixedSpace K) := by
    exact_mod_cast hr
  refine ⟨r, fun w => ?_⟩
  set fract_g := ZSpan.fract (latticeBasis K) g with hfract_def
  set diff := f - algebraMap K _ (c₁ + algebraMap (𝓞 K) K r) with hdiff_def
  have halg : ringEquiv_mixedSpace K diff = fract_g := by
    rw [hfract_def, ZSpan.fract_apply, hdiff_def]
    have key : ringEquiv_mixedSpace K (f - algebraMap K _ (c₁ + algebraMap (𝓞 K) K r)) =
      g - mixedEmbedding K (algebraMap (𝓞 K) K r) := by
      simp only [hg_def, map_sub, map_add, mixedEmbedding_eq_algebraMap_comp]
      ring
    rw [key, hr']
  have hfract_bound : ‖fract_g‖ ≤ coveringBound K :=
    le_trans (ZSpan.norm_fract_le (latticeBasis K) g) (le_max_right _ _)
  suffices h : ‖diff w‖ ≤ ‖fract_g‖ by
    simp only [hdiff_def] at h
    exact le_trans h hfract_bound
  by_cases hw : w.IsReal
  ·
    have heq : extensionEmbeddingOfIsReal hw (diff w) = fract_g.1 ⟨w, hw⟩ := by
      have := congr_arg Prod.fst halg
      simp [ringEquiv_mixedSpace_apply] at this
      exact congr_fun this ⟨w, hw⟩
    rw [← (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), heq]
    exact le_trans (norm_le_pi_norm fract_g.1 ⟨w, hw⟩) (le_max_left _ _)
  ·
    have hwc := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw
    have heq : extensionEmbedding w (diff w) = fract_g.2 ⟨w, hwc⟩ := by
      have := congr_arg Prod.snd halg
      simp [ringEquiv_mixedSpace_apply] at this
      exact congr_fun this ⟨w, hwc⟩
    rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), heq]
    exact le_trans (norm_le_pi_norm fract_g.2 ⟨w, hwc⟩) (le_max_right _ _)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[crt_covering](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma crt_covering
  [Field K]
  [NumberField K]
-- given
  (a : adeleRing (K := K)) :
-- imply
  ∃ c : K, (∀ w : InfinitePlace K, ‖a.1 w - algebraMap K w.Completion c‖ ≤ coveringBound K) ∧ (∀ v : HeightOneSpectrum (𝓞 K), (a.2 v - algebraMap K (v.adicCompletion K) c) ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
-- proof
  obtain ⟨c₁, hfin₁⟩ := crt_finite_places_covering K a.2
  obtain ⟨r, hinf⟩ := lattice_covering_infinite_places K a.1 c₁
  refine ⟨c₁ + algebraMap (𝓞 K) K r, hinf, fun v => ?_⟩
  rw [map_add]
  have h1 : a.2 v - algebraMap K (v.adicCompletion K) c₁ ∈
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := hfin₁ v
  have h2 : algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) ∈
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    change (algebraMap (𝓞 K) (v.adicCompletion K) r : v.adicCompletion K) ∈ _
    exact v.coe_mem_adicCompletionIntegers r
  have : a.2 v - (algebraMap K (v.adicCompletion K) c₁ +
    algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r)) =
    (a.2 v - algebraMap K (v.adicCompletion K) c₁) -
    algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) := by ring
  rw [this]
  exact sub_mem h1 h2

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adeles_compact_fundamental_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adeles_compact_fundamental_domain
  [Field K]
  [NumberField K] :
-- imply
  ∃ W : Set (adeleRing (K := K)), IsCompact W ∧ ∀ a : adeleRing (K := K), ∃ c : K, a - algebraMap K _ c ∈ W := by
-- proof
  refine ⟨(Set.pi Set.univ (fun (v : InfinitePlace K) =>
    Metric.closedBall (0 : v.Completion) (coveringBound K))) ×ˢ
    {a : FiniteAdeleRing (𝓞 K) K |
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}, ?_, ?_⟩
  ·
    apply IsCompact.prod
    · exact isCompact_univ_pi (fun v => isCompact_closedBall 0 (coveringBound K))
    · exact isCompact_finiteAdeleRing_integralSet
  ·
    intro a
    obtain ⟨c, hinf, hfin⟩ := crt_covering a
    exact ⟨c, ⟨fun w _ => by
      simp only [Metric.mem_closedBall, dist_zero_right]; exact hinf w, fun v => hfin v⟩⟩

end NumberField.Adeles

namespace NumberField.Adeles

/--
[principalAdeles_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma principalAdeles_cocompact
  [Field K]
  [NumberField K] :
-- imply
  CompactSpace ((adeleRing (K := K)) ⧸ (principalSubgroup (K := K))) := by
-- proof
  obtain ⟨W, hW_compact, hW_surj⟩ := adeles_compact_fundamental_domain (K := K)
  rw [← isCompact_univ_iff]
  have himg : Set.univ = (QuotientAddGroup.mk (s := principalSubgroup (K := K))) '' W := by
    ext q
    simp only [Set.mem_univ, true_iff, Set.mem_image]
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨c, hc⟩ := hW_surj a
    refine ⟨a - algebraMap K _ c, hc, ?_⟩
    simp only [QuotientAddGroup.mk_sub]
    rw [sub_eq_self]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨c, rfl⟩
  rw [himg]
  exact hW_compact.image continuous_quotient_mk'

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adeleRing_algebra_base_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adeleRing_algebra_base_algebraMap
  [Field K]
  [NumberField K]
  {L : Type*}
  [Field L]
  [NumberField L]
  [Algebra K L] :
-- imply
  algebraMap K (AdeleRing (𝓞 L) L) = (algebraMap L (AdeleRing (𝓞 L) L)).comp (algebraMap K L) :=
-- proof
  rfl

end NumberField.Adeles

namespace NumberField.Adeles

/--
[mem_adicCompletionIntegers_iff_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma mem_adicCompletionIntegers_iff_norm_le_one
  [Field K]
  [NumberField K]
  {vi : HeightOneSpectrum (𝓞 K)}
  {x : vi.adicCompletion K} :
-- imply
  x ∈ vi.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
-- proof
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valued.toNormedField.norm_le_one_iff (L := vi.adicCompletion K)
    (Γ₀ := WithZero (Multiplicative ℤ))).symm

end NumberField.Adeles

namespace NumberField.Adeles

/--
[exists_strategic_adele](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma exists_strategic_adele
  [Field K]
  [NumberField K]
  {B : ℝ}
  {S : Finset (Place K)}
  {w : Place K}
-- given
  (hB : 0 < B)
  (hw : w ∉ S)
  (ε : (v : Place K) → v ∈ S → ℝ)
  (hε : ∀ v (hv : v ∈ S), 0 < ε v hv) :
-- imply
  ∃ (z : adeleRing (K := K)), adelicAbsVal z > B ∧ (∀ v (hv : v ∈ S), placeNormAdele v z ≤ ε v hv) ∧ (∀ v : Place K, v ∉ S → v ≠ w → placeNormAdele v z ≤ 1) ∧ (Function.mulSupport (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => ‖z.2 v‖)).Finite := by
-- proof
  classical
  obtain ⟨vi_w⟩ | ⟨w_inf⟩ := w
  ·
    let inf_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        Classical.choose (NormedField.exists_norm_lt w'.Completion (hε _ hS))
      else 1
    let S_fin := S.preimage Place.finite (fun a _ b _ h => Place.finite.inj h)
    let s_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        Classical.choose (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hS) one_pos))
      else 1
    let P_inf : ℝ := ∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult
    have hP_inf_pos : 0 < P_inf := by
      apply Finset.prod_pos
      intro w' _
      apply pow_pos
      simp only [inf_fn]
      split_ifs with hS
      · exact (Classical.choose_spec
        (NormedField.exists_norm_lt w'.Completion (hε _ hS))).1
      · simp [norm_one]
    let P_fin : ℝ := ∏ vi ∈ S_fin, ‖s_fn vi‖
    have hP_fin_pos : 0 < P_fin := by
      apply Finset.prod_pos
      intro vi hvi
      simp only [S_fin, Finset.mem_preimage] at hvi
      simp only [s_fn, dif_pos hvi]
      letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
        (WithZero (Multiplicative ℤ))
      exact (Classical.choose_spec
        (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hvi) one_pos))).1
    let P : ℝ := P_inf * P_fin
    have hP_pos : 0 < P := mul_pos hP_inf_pos hP_fin_pos
    letI := Valued.toNontriviallyNormedField (vi_w.adicCompletion K)
      (WithZero (Multiplicative ℤ))
    let vi_w_elem := Classical.choose
      (NormedField.exists_lt_norm (vi_w.adicCompletion K) ((B + 1) / P))
    have hw_spec : (B + 1) / P < ‖vi_w_elem‖ :=
      Classical.choose_spec
        (NormedField.exists_lt_norm (vi_w.adicCompletion K) ((B + 1) / P))
    let fin_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then s_fn vi
      else if h : vi = vi_w then h ▸ vi_w_elem
      else 1
    have fin_mem : ∀ᶠ vi in Filter.cofinite,
      fin_fn vi ∈ vi.adicCompletionIntegers K := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset
      · exact (S_fin.finite_toSet).union (Set.finite_singleton vi_w)
      · intro vi hvi
        simp only [Set.mem_setOf_eq] at hvi
        by_contra h_not
        simp only [Set.mem_union, Finset.mem_coe, S_fin, Finset.mem_preimage,
          Set.mem_singleton_iff] at h_not
        push Not at h_not
        have h1 : ¬ Place.finite vi ∈ S := h_not.1
        have h2 : ¬ vi = vi_w := h_not.2
        simp only [fin_fn, dif_neg h1, dif_neg h2] at hvi
        exact hvi ((vi.adicCompletionIntegers K).one_mem')
    let z : adeleRing (K := K) := (inf_fn, RestrictedProduct.mk fin_fn fin_mem)
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    ·
      unfold adelicAbsVal
      simp only [z]
      have hinf_eq : ∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult = P_inf := rfl
      let g : HeightOneSpectrum (𝓞 K) → ℝ := fun vi => ‖fin_fn vi‖
      have hsupp : Function.mulSupport g ⊆ ↑(S_fin ∪ {vi_w}) := by
        intro vi hvi
        simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
          S_fin, Finset.mem_preimage, Set.mem_singleton_iff]
        by_contra h_not
        push Not at h_not
        have h1 : ¬ Place.finite vi ∈ S := h_not.1
        have h2 : ¬ vi = vi_w := h_not.2
        simp only [g, fin_fn, dif_neg h1, dif_neg h2, norm_one] at hvi
        exact hvi rfl
      have hfin_eq : ∏ᶠ vi, g vi = ∏ vi ∈ S_fin ∪ {vi_w}, g vi :=
        finprod_eq_prod_of_mulSupport_subset g hsupp
      have hvi_w_notin : vi_w ∉ S_fin := by
        simp only [S_fin, Finset.mem_preimage]
        exact hw
      have hsplit : ∏ vi ∈ S_fin ∪ {vi_w}, g vi =
        (∏ vi ∈ S_fin, g vi) * (∏ vi ∈ ({vi_w} : Finset _), g vi) :=
        Finset.prod_union (Finset.disjoint_singleton_right.mpr hvi_w_notin)
      have hsingleton : ∏ vi ∈ ({vi_w} : Finset _), g vi = ‖vi_w_elem‖ := by
        simp only [Finset.prod_singleton, g, fin_fn, dif_neg hw, dite_true]
      have hS_prod : ∏ vi ∈ S_fin, g vi = P_fin := by
        apply Finset.prod_congr rfl
        intro vi hvi
        simp only [S_fin, Finset.mem_preimage] at hvi
        simp only [g, fin_fn, dif_pos hvi]
      have hfinprod_val : ∏ᶠ vi, g vi = P_fin * ‖vi_w_elem‖ := by
        rw [hfin_eq, hsplit, hS_prod, hsingleton]
      have hmk : ∀ vi, ‖(RestrictedProduct.mk fin_fn fin_mem) vi‖ = g vi := by
        intro vi; simp [g, RestrictedProduct.mk_apply]
      have hfp_eq : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
        ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) = P_fin * ‖vi_w_elem‖ := by
        trans (∏ᶠ vi, g vi)
        · exact finprod_congr hmk
        · exact hfinprod_val
      have hbound : P_inf * (P_fin * ‖vi_w_elem‖) > B := by
        calc B < B + 1 := by linarith
          _ = (B + 1) / P * P := by rw [div_mul_cancel₀]; exact ne_of_gt hP_pos
          _ < ‖vi_w_elem‖ * P := mul_lt_mul_of_pos_right hw_spec hP_pos
          _ = ‖vi_w_elem‖ * (P_inf * P_fin) := rfl
          _ = P_inf * (P_fin * ‖vi_w_elem‖) := by ring
      have hgoal_eq : (∏ x : InfinitePlace K, ‖inf_fn x‖ ^ x.mult) *
        (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
          ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) =
        P_inf * (P_fin * ‖vi_w_elem‖) := by
        rw [hinf_eq]; congr 1
      exact hgoal_eq ▸ hbound
    ·
      intro v hv
      match v, hv with
      | .infinite w', hv =>
        show ‖inf_fn w'‖ ≤ ε (Place.infinite w') hv
        simp only [inf_fn, dif_pos hv]
        exact le_of_lt (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hv))).2
      | .finite vi, hv =>
        show ‖fin_fn vi‖ ≤ ε (Place.finite vi) hv
        simp only [fin_fn, s_fn, dif_pos hv]
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        have spec := Classical.choose_spec (NormedField.exists_norm_lt
          (vi.adicCompletion K) (lt_min (hε (.finite vi) hv) one_pos))
        exact le_of_lt (lt_of_lt_of_le spec.2 (min_le_left _ _))
    ·
      intro v hvS hne
      match v, hvS, hne with
      | .infinite w', hvS, _ =>
        show ‖inf_fn w'‖ ≤ 1
        simp only [inf_fn, dif_neg hvS, norm_one, le_refl]
      | .finite vi, hvS, hne =>
        show ‖fin_fn vi‖ ≤ 1
        have hnotW : vi ≠ vi_w := fun h => hne (congrArg Place.finite h)
        simp only [fin_fn, dif_neg hvS, dif_neg hnotW, norm_one, le_refl]
    ·
      apply Set.Finite.subset ((S_fin ∪ {vi_w}).finite_toSet)
      intro vi hvi
      simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
      change ‖fin_fn vi‖ ≠ 1 at hvi
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
        S_fin, Finset.mem_preimage, Set.mem_singleton_iff]
      by_contra h_not
      push Not at h_not
      have h1 : ¬ Place.finite vi ∈ S := h_not.1
      have h2 : ¬ vi = vi_w := h_not.2
      simp only [fin_fn, dif_neg h1, dif_neg h2, norm_one] at hvi
      exact hvi rfl
  ·
    let inf_S_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        Classical.choose (NormedField.exists_norm_lt w'.Completion (hε _ hS))
      else 1
    let S_fin := S.preimage Place.finite (fun a _ b _ h => Place.finite.inj h)
    let fin_fn : (vi : HeightOneSpectrum (𝓞 K)) → vi.adicCompletion K := fun vi =>
      if hS : Place.finite vi ∈ S then
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K) (WithZero (Multiplicative ℤ))
        Classical.choose (NormedField.exists_norm_lt (vi.adicCompletion K)
          (lt_min (hε (.finite vi) hS) one_pos))
      else 1
    let P_inf_other : ℝ := ∏ w' : InfinitePlace K, ‖inf_S_fn w'‖ ^ w'.mult
    have hP_inf_other_pos : 0 < P_inf_other := by
      apply Finset.prod_pos; intro w' _; apply pow_pos
      simp only [inf_S_fn]; split_ifs with hS
      · exact (Classical.choose_spec
        (NormedField.exists_norm_lt w'.Completion (hε _ hS))).1
      · simp [norm_one]
    let P_fin : ℝ := ∏ vi ∈ S_fin, ‖fin_fn vi‖
    have hP_fin_pos : 0 < P_fin := by
      apply Finset.prod_pos; intro vi hvi
      simp only [S_fin, Finset.mem_preimage] at hvi
      simp only [fin_fn, dif_pos hvi]
      letI := Valued.toNontriviallyNormedField (vi.adicCompletion K) (WithZero (Multiplicative ℤ))
      exact (Classical.choose_spec (NormedField.exists_norm_lt (vi.adicCompletion K)
        (lt_min (hε (.finite vi) hvi) one_pos))).1
    let P : ℝ := P_inf_other * P_fin
    have hP_pos : 0 < P := mul_pos hP_inf_other_pos hP_fin_pos
    let w_inf_elem := Classical.choose
      (NormedField.exists_lt_norm w_inf.Completion ((B + 1) / P + 1))
    have hw_spec : (B + 1) / P + 1 < ‖w_inf_elem‖ :=
      Classical.choose_spec (NormedField.exists_lt_norm w_inf.Completion ((B + 1) / P + 1))
    have hw_gt_one : 1 < ‖w_inf_elem‖ := by
      calc 1 ≤ (B + 1) / P + 1 := le_add_of_nonneg_left (div_nonneg (by linarith) (le_of_lt hP_pos))
        _ < ‖w_inf_elem‖ := hw_spec
    have hw_norm_pos : 0 < ‖w_inf_elem‖ := by linarith
    let inf_fn : (w' : InfinitePlace K) → w'.Completion := fun w' =>
      if hS : Place.infinite w' ∈ S then
        inf_S_fn w'
      else if h : w' = w_inf then h ▸ w_inf_elem
      else 1
    have fin_mem : ∀ᶠ vi in Filter.cofinite,
      fin_fn vi ∈ vi.adicCompletionIntegers K := by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset
      · exact (S.preimage Place.finite
        (fun a _ b _ h => Place.finite.inj h)).finite_toSet
      · intro vi hvi
        simp only [Set.mem_setOf_eq] at hvi
        by_contra h_not
        simp only [Finset.mem_coe, Finset.mem_preimage] at h_not
        simp only [fin_fn, dif_neg h_not] at hvi
        exact hvi ((vi.adicCompletionIntegers K).one_mem')
    let z : adeleRing (K := K) := (inf_fn, RestrictedProduct.mk fin_fn fin_mem)
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    ·
      unfold adelicAbsVal
      simp only [z]
      have hinf_S : ∀ w' : InfinitePlace K, w' ≠ w_inf →
        ‖inf_fn w'‖ = ‖inf_S_fn w'‖ := by
        intro w' hw'
        simp only [inf_fn]
        rw [dite_eq_ite]
        split_ifs with hS
        · simp only [inf_S_fn, dif_pos hS]
        · simp only [inf_S_fn, dif_neg (show ¬ Place.infinite w' ∈ S from by
          intro hc; exact hS hc), norm_one]
      have hinf_w : ‖inf_fn w_inf‖ = ‖w_inf_elem‖ := by
        simp only [inf_fn, dif_neg hw, dite_true]
      let g : HeightOneSpectrum (𝓞 K) → ℝ := fun vi => ‖fin_fn vi‖
      have hsupp : Function.mulSupport g ⊆ ↑S_fin := by
        intro vi hvi
        simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
        simp only [Finset.mem_coe, S_fin, Finset.mem_preimage]
        by_contra h_not
        simp only [g, fin_fn, dif_neg h_not, norm_one] at hvi
        exact hvi rfl
      have hfin_eq : ∏ᶠ vi, g vi = ∏ vi ∈ S_fin, g vi :=
        finprod_eq_prod_of_mulSupport_subset g hsupp
      have hS_prod : ∏ vi ∈ S_fin, g vi = P_fin := by
        apply Finset.prod_congr rfl; intro vi hvi
        simp only [S_fin, Finset.mem_preimage] at hvi
        simp only [g, fin_fn, dif_pos hvi]
      have hfinprod_val : ∏ᶠ vi, g vi = P_fin := by
        rw [hfin_eq, hS_prod]
      have hmk : ∀ vi, ‖(RestrictedProduct.mk fin_fn fin_mem) vi‖ = g vi := by
        intro vi; simp [g, RestrictedProduct.mk_apply]
      have hfp_eq : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
        ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) = P_fin := by
        trans (∏ᶠ vi, g vi)
        · exact finprod_congr hmk
        · exact hfinprod_val
      have hinf_S_at_w : ‖inf_S_fn w_inf‖ = 1 := by
        simp only [inf_S_fn, dif_neg hw, norm_one]
      have hinf_prod_eq : (∏ w' : InfinitePlace K, ‖inf_fn w'‖ ^ w'.mult) =
        P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult := by
        have hmem : w_inf ∈ Finset.univ := Finset.mem_univ w_inf
        rw [← Finset.mul_prod_erase _ _ hmem]
        rw [hinf_w]
        have hlhs : ∏ x ∈ Finset.univ.erase w_inf, ‖inf_fn x‖ ^ x.mult =
          ∏ x ∈ Finset.univ.erase w_inf, ‖inf_S_fn x‖ ^ x.mult := by
          apply Finset.prod_congr rfl
          intro w' hw'
          rw [Finset.mem_erase] at hw'
          rw [hinf_S w' hw'.1]
        rw [hlhs]
        have hP_factor : P_inf_other =
          (fun w' => ‖inf_S_fn w'‖ ^ w'.mult) w_inf *
          ∏ x ∈ Finset.univ.erase w_inf, (fun w' => ‖inf_S_fn w'‖ ^ w'.mult) x :=
          (Finset.mul_prod_erase _ _ hmem).symm
        simp only at hP_factor
        rw [hP_factor, hinf_S_at_w, one_pow, one_mul]
        ring
      have hbound : P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin > B := by
        have h_mult_pos : 0 < w_inf.mult := w_inf.mult_pos
        have hpow_ge : ‖w_inf_elem‖ ^ w_inf.mult ≥ ‖w_inf_elem‖ :=
          le_self_pow₀ (le_of_lt hw_gt_one) h_mult_pos.ne'
        calc B < B + 1 := by linarith
          _ = (B + 1) / P * P := by rw [div_mul_cancel₀]; exact ne_of_gt hP_pos
          _ < ((B + 1) / P + 1) * P := by nlinarith
          _ < ‖w_inf_elem‖ * P := mul_lt_mul_of_pos_right hw_spec hP_pos
          _ = ‖w_inf_elem‖ * (P_inf_other * P_fin) := rfl
          _ ≤ ‖w_inf_elem‖ ^ w_inf.mult * (P_inf_other * P_fin) := by
            exact mul_le_mul_of_nonneg_right hpow_ge (le_of_lt hP_pos)
          _ = P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin := by ring
      have hgoal_eq : (∏ x : InfinitePlace K, ‖inf_fn x‖ ^ x.mult) *
        (∏ᶠ (v : HeightOneSpectrum (𝓞 K)),
          ‖(RestrictedProduct.mk fin_fn fin_mem) v‖) =
        P_inf_other * ‖w_inf_elem‖ ^ w_inf.mult * P_fin := by
        rw [hinf_prod_eq]; ring_nf; rw [hfp_eq]
      exact hgoal_eq ▸ hbound
    ·
      intro v hv
      match v, hv with
      | .infinite w', hv =>
        show ‖inf_fn w'‖ ≤ ε (Place.infinite w') hv
        simp only [inf_fn, inf_S_fn, dif_pos hv]
        exact le_of_lt (Classical.choose_spec
          (NormedField.exists_norm_lt w'.Completion (hε _ hv))).2
      | .finite vi, hv =>
        show ‖fin_fn vi‖ ≤ ε (Place.finite vi) hv
        simp only [fin_fn, dif_pos hv]
        letI := Valued.toNontriviallyNormedField (vi.adicCompletion K)
          (WithZero (Multiplicative ℤ))
        have spec := Classical.choose_spec (NormedField.exists_norm_lt
          (vi.adicCompletion K) (lt_min (hε (.finite vi) hv) one_pos))
        exact le_of_lt (lt_of_lt_of_le spec.2 (min_le_left _ _))
    ·
      intro v hvS hne
      match v, hvS, hne with
      | .infinite w', hvS, hne =>
        show ‖inf_fn w'‖ ≤ 1
        have hnotW : w' ≠ w_inf := fun h => hne (congrArg Place.infinite h)
        simp only [inf_fn, dif_neg hvS, dif_neg hnotW, norm_one, le_refl]
      | .finite vi, hvS, _ =>
        show ‖fin_fn vi‖ ≤ 1
        simp only [fin_fn, dif_neg hvS, norm_one, le_refl]
    ·
      apply Set.Finite.subset (S_fin.finite_toSet)
      intro vi hvi
      simp only [Function.mulSupport, Set.mem_setOf_eq] at hvi
      change ‖fin_fn vi‖ ≠ 1 at hvi
      simp only [Finset.mem_coe, S_fin, Finset.mem_preimage]
      by_contra h_not
      simp only [fin_fn, dif_neg h_not, norm_one] at hvi
      exact hvi rfl

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adicAbv_le_one_of_mem_integers_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adicAbv_le_one_of_mem_integers_algebraMap
  [Field K]
  [NumberField K]
  {vi : HeightOneSpectrum (𝓞 K)}
  {x : K}
-- given
  (hx : algebraMap K (vi.adicCompletion K) x ∈ (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))) :
-- imply
  NumberField.HeightOneSpectrum.adicAbv K vi x ≤ 1 := by
-- proof
  rw [NumberField.HeightOneSpectrum.adicAbv_def]
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K)] at hx
  have : algebraMap K (vi.adicCompletion K) x = (x : vi.adicCompletion K) := rfl
  rw [this] at hx
  rw [vi.valuedAdicCompletion_eq_valuation' x] at hx
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal vi)).mpr hx

end NumberField.Adeles

namespace NumberField.Adeles

/--
[placeNorm_infinite_eq_norm_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma placeNorm_infinite_eq_norm_algebraMap
  [Field K]
  [NumberField K]
  {w : InfinitePlace K}
  {x : K} :
-- imply
  w x = ‖algebraMap K w.Completion x‖ := by
-- proof
  rw [show algebraMap K w.Completion x =
    (↑((WithAbs.equiv w.1).symm x) : w.Completion) from rfl]
  rw [InfinitePlace.Completion.norm_coe]; simp

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adeles_K_plus_unit_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adeles_K_plus_unit_ball
  [Field K]
  [NumberField K]
  {S : Finset (Place K)}
-- given
  (a : (v : Place K) → v ∈ S → K) :
-- imply
  ∃ (c : K), (∀ v (hv : v ∈ S), placeNorm v (c - a v hv) ≤ coveringBound K) ∧ (∀ v : Place K, v ∉ S → placeNorm v c ≤ coveringBound K) := by
-- proof
  let finPartFun : ∀ vi : HeightOneSpectrum (𝓞 K), vi.adicCompletion K := fun vi =>
    if h : Place.finite vi ∈ S
    then algebraMap K (vi.adicCompletion K) (a (.finite vi) h)
    else 0
  have hfin_mem : ∀ᶠ vi in Filter.cofinite,
    finPartFun vi ∈ (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) := by
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.Finite.preimage
      (fun v₁ _ v₂ _ h => Place.finite.inj h) S.finite_toSet)
    intro vi hvi
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe] at *
    by_contra hmem
    exact hvi (by simp only [finPartFun, dif_neg hmem]; exact (vi.adicCompletionIntegers K).zero_mem)
  let b : adeleRing (K := K) :=
    ((fun w => if h : Place.infinite w ∈ S
      then algebraMap K w.Completion (a (.infinite w) h) else 0),
      ⟨finPartFun, hfin_mem⟩)
  obtain ⟨c, hinf, hfin⟩ := crt_covering b
  refine ⟨c, ?_, ?_⟩
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w (c - a (.infinite w) hv) ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_pos hv] at hinf_w
      rwa [placeNorm_infinite_eq_norm_algebraMap, RingHom.map_sub, norm_sub_rev]
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi (c - a (.finite vi) hv) ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_pos hv] at hfin_vi
      rw [show c - a (.finite vi) hv = -(a (.finite vi) hv - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (a (.finite vi) hv - c)
        (by rw [RingHom.map_sub]; exact hfin_vi)) (one_le_coveringBound K)
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w c ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_neg hv] at hinf_w
      rw [placeNorm_infinite_eq_norm_algebraMap]
      calc ‖algebraMap K w.Completion c‖
        = ‖0 - algebraMap K w.Completion c‖ := by rw [zero_sub, norm_neg]
        _ ≤ coveringBound K := hinf_w
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi c ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_neg hv] at hfin_vi
      rw [show c = -(0 - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (0 - c)
        (by rw [RingHom.map_sub, RingHom.map_zero]; exact hfin_vi)) (one_le_coveringBound K)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adelic_scaling_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adelic_scaling_decomposition
  [Field K]
  [NumberField K]
  {u : K}
  {S : Finset (Place K)}
-- given
  (hu : u ≠ 0)
  (a : (v : Place K) → v ∈ S → K) :
-- imply
  ∃ (x : K), (∀ v (hv : v ∈ S), placeNorm v (x - a v hv) ≤ placeNorm v u * coveringBound K) ∧ (∀ v : Place K, v ∉ S → placeNorm v x ≤ placeNorm v u * coveringBound K) := by
-- proof
  obtain ⟨c, hc_S, hc_T⟩ := adeles_K_plus_unit_ball S (fun v hv => u⁻¹ * a v hv)
  refine ⟨u * c, fun v hv => ?_, fun v hv => ?_⟩
  ·
    have key : u * c - a v hv = u * (c - u⁻¹ * a v hv) := by field_simp
    rw [key, placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_S v hv) (placeNorm_nonneg v u)
  ·
    rw [placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_T v hv) (placeNorm_nonneg v u)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[placeNorm_finite_le_one_imp_mem_integers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma placeNorm_finite_le_one_imp_mem_integers
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {x : K}
-- given
  (hx : placeNorm (.finite v) x ≤ 1) :
-- imply
  (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
-- proof
  rw [SetLike.mem_coe, mem_adicCompletionIntegers_iff_norm_le_one]
  show ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v‖ ≤ 1
  have : (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v = algebraMap K (v.adicCompletion K) x := rfl
  rw [this]
  have : algebraMap K (v.adicCompletion K) x = FinitePlace.embedding v x := rfl
  rwa [this, FinitePlace.norm_embedding]

end NumberField.Adeles

namespace NumberField.Adeles

/--
[algebraMap_finiteAdeleRing_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma algebraMap_finiteAdeleRing_apply
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {x : K} :
-- imply
  (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v = algebraMap K (v.adicCompletion K) x :=
-- proof
  rfl

end NumberField.Adeles

namespace NumberField.Adeles

/--
[norm_algebraMap_finiteAdeleRing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma norm_algebraMap_finiteAdeleRing_eq
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {x : K} :
-- imply
  ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v‖ = placeNorm (.finite v) x := by
-- proof
  show ‖algebraMap K (v.adicCompletion K) x‖ = HeightOneSpectrum.adicAbv K v x
  rw [show algebraMap K (v.adicCompletion K) x = FinitePlace.embedding v x from rfl]
  rw [FinitePlace.norm_embedding]

end NumberField.Adeles

namespace NumberField.Adeles

/--
[strong_approx_integral_to_mem_integers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma strong_approx_integral_to_mem_integers
  [Field K]
  [NumberField K]
  {x : K}
  {S : Finset (HeightOneSpectrum (𝓞 K))}
-- given
  (hx : ∀ (v : HeightOneSpectrum (𝓞 K)), v ∉ S → placeNorm (.finite v) x ≤ 1) :
-- imply
  ∀ (v : HeightOneSpectrum (𝓞 K)), v ∉ S → (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
-- proof
  fun v hv => placeNorm_finite_le_one_imp_mem_integers v x (hx v hv)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[norm_algebraMap_finiteAdeleRing_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma norm_algebraMap_finiteAdeleRing_sub
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {x y : K} :
-- imply
  ‖(algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v - (algebraMap K (FiniteAdeleRing (𝓞 K) K) y) v‖ = placeNorm (.finite v) (x - y) := by
-- proof
  have : (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v -
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) y) v =
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) (x - y)) v := by
    show algebraMap K (v.adicCompletion K) x - algebraMap K (v.adicCompletion K) y =
      algebraMap K (v.adicCompletion K) (x - y)
    rw [map_sub]
  rw [this, norm_algebraMap_finiteAdeleRing_eq]

end NumberField.Adeles

namespace NumberField.Adeles

/--
[algebraMap_finiteAdeleRing_sub_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma algebraMap_finiteAdeleRing_sub_apply
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {x y : K} :
-- imply
  (algebraMap K (FiniteAdeleRing (𝓞 K) K) (x - y)) v = (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v - (algebraMap K (FiniteAdeleRing (𝓞 K) K) y) v := by
-- proof
  show algebraMap K (v.adicCompletion K) (x - y) =
    algebraMap K (v.adicCompletion K) x - algebraMap K (v.adicCompletion K) y
  rw [map_sub]

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adeles_K_plus_unit_ball_finite_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adeles_K_plus_unit_ball_finite_le_one
  [Field K]
  [NumberField K]
  {S : Finset (Place K)}
-- given
  (a : (v : Place K) → v ∈ S → K) :
-- imply
  ∃ (c : K), (∀ v (hv : v ∈ S), placeNorm v (c - a v hv) ≤ coveringBound K) ∧ (∀ v : Place K, v ∉ S → placeNorm v c ≤ coveringBound K) ∧ (∀ (vi : HeightOneSpectrum (𝓞 K)), Place.finite vi ∉ S → placeNorm (.finite vi) c ≤ 1) := by
-- proof
  let finPartFun : ∀ vi : HeightOneSpectrum (𝓞 K), vi.adicCompletion K := fun vi =>
    if h : Place.finite vi ∈ S
    then algebraMap K (vi.adicCompletion K) (a (.finite vi) h)
    else 0
  have hfin_mem : ∀ᶠ vi in Filter.cofinite,
    finPartFun vi ∈ (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) := by
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.Finite.preimage
      (fun v₁ _ v₂ _ h => Place.finite.inj h) S.finite_toSet)
    intro vi hvi
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe] at *
    by_contra hmem
    exact hvi (by simp only [finPartFun, dif_neg hmem]; exact (vi.adicCompletionIntegers K).zero_mem)
  let b : adeleRing (K := K) :=
    ((fun w => if h : Place.infinite w ∈ S
      then algebraMap K w.Completion (a (.infinite w) h) else 0),
      ⟨finPartFun, hfin_mem⟩)
  obtain ⟨c, hinf, hfin⟩ := crt_covering b
  refine ⟨c, ?_, ?_, ?_⟩
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w (c - a (.infinite w) hv) ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_pos hv] at hinf_w
      rwa [placeNorm_infinite_eq_norm_algebraMap, RingHom.map_sub, norm_sub_rev]
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi (c - a (.finite vi) hv) ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_pos hv] at hfin_vi
      rw [show c - a (.finite vi) hv = -(a (.finite vi) hv - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (a (.finite vi) hv - c)
        (by rw [RingHom.map_sub]; exact hfin_vi)) (one_le_coveringBound K)
  ·
    intro v hv
    match v with
    | .infinite w =>
      have hinf_w := hinf w
      show w c ≤ coveringBound K
      change ‖(if h : Place.infinite w ∈ S
        then algebraMap K w.Completion (a (.infinite w) h) else 0) -
        algebraMap K w.Completion c‖ ≤ coveringBound K at hinf_w
      simp only [dif_neg hv] at hinf_w
      rw [placeNorm_infinite_eq_norm_algebraMap]
      calc ‖algebraMap K w.Completion c‖
        = ‖0 - algebraMap K w.Completion c‖ := by rw [zero_sub, norm_neg]
        _ ≤ coveringBound K := hinf_w
    | .finite vi =>
      have hfin_vi := hfin vi
      show NumberField.HeightOneSpectrum.adicAbv K vi c ≤ coveringBound K
      change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
        (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
      simp only [finPartFun, dif_neg hv] at hfin_vi
      rw [show c = -(0 - c) from by ring]
      rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
      exact le_trans (adicAbv_le_one_of_mem_integers_algebraMap vi (0 - c)
        (by rw [RingHom.map_sub, RingHom.map_zero]; exact hfin_vi)) (one_le_coveringBound K)
  ·
    intro vi hvi
    have hfin_vi := hfin vi
    show NumberField.HeightOneSpectrum.adicAbv K vi c ≤ 1
    change (finPartFun vi - algebraMap K (vi.adicCompletion K) c) ∈
      (vi.adicCompletionIntegers K : Set (vi.adicCompletion K)) at hfin_vi
    simp only [finPartFun, dif_neg hvi] at hfin_vi
    rw [show c = -(0 - c) from by ring]
    rw [(NumberField.HeightOneSpectrum.adicAbv K vi).map_neg]
    exact adicAbv_le_one_of_mem_integers_algebraMap vi (0 - c)
      (by rw [RingHom.map_sub, RingHom.map_zero]; exact hfin_vi)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[adelic_scaling_decomposition_finite_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma adelic_scaling_decomposition_finite_le_one
  [Field K]
  [NumberField K]
  {u : K}
  {S : Finset (Place K)}
-- given
  (hu : u ≠ 0)
  (a : (v : Place K) → v ∈ S → K) :
-- imply
  ∃ (x : K), (∀ v (hv : v ∈ S), placeNorm v (x - a v hv) ≤ placeNorm v u * coveringBound K) ∧ (∀ v : Place K, v ∉ S → placeNorm v x ≤ placeNorm v u * coveringBound K) ∧ (∀ (vi : HeightOneSpectrum (𝓞 K)), Place.finite vi ∉ S → placeNorm (.finite vi) x ≤ placeNorm (.finite vi) u * 1) := by
-- proof
  obtain ⟨c, hc_S, hc_T, hc_fin⟩ := adeles_K_plus_unit_ball_finite_le_one S (fun v hv => u⁻¹ * a v hv)
  refine ⟨u * c, fun v hv => ?_, fun v hv => ?_, fun vi hvi => ?_⟩
  · have key : u * c - a v hv = u * (c - u⁻¹ * a v hv) := by field_simp
    rw [key, placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_S v hv) (placeNorm_nonneg v u)
  · rw [placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_T v hv) (placeNorm_nonneg v u)
  · rw [placeNorm_mul]
    exact mul_le_mul_of_nonneg_left (hc_fin vi hvi) (placeNorm_nonneg (.finite vi) u)

end NumberField.Adeles

namespace NumberField.Adeles

/--
[global_field_dense_in_infiniteAdeleRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma global_field_dense_in_infiniteAdeleRing
  [Field K]
  [NumberField K] :
-- imply
  Dense (Set.range (algebraMap K (InfiniteAdeleRing K))) :=
-- proof
  InfiniteAdeleRing.denseRange_algebraMap K

end NumberField.Adeles

namespace NumberField.Adeles

/--
[isOpen_placeIntegerSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma isOpen_placeIntegerSet
  [Field K]
  [NumberField K]
  {v : Place K} :
-- imply
  IsOpen (placeIntegerSet v) := by
-- proof
  cases v with
  | finite vi => exact Valued.isOpen_valuationSubring _
  | infinite _ => exact isOpen_univ

end NumberField.Adeles

namespace NumberField.Adeles

/--
[placeNorm_le_one_imp_mem_placeIntegerSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma placeNorm_le_one_imp_mem_placeIntegerSet
  [Field K]
  [NumberField K]
  {v : Place K}
  {x : K}
-- given
  (hx : placeNorm v x ≤ 1) :
-- imply
  embedAtPlace v x ∈ placeIntegerSet v := by
-- proof
  cases v with
  | finite vi =>
    show algebraMap K (vi.adicCompletion K) x ∈
      (vi.adicCompletionIntegers K : Set (vi.adicCompletion K))
    rw [SetLike.mem_coe, mem_adicCompletionIntegers_iff_norm_le_one]
    rw [show algebraMap K (vi.adicCompletion K) x = FinitePlace.embedding vi x from rfl,
      FinitePlace.norm_embedding]
    exact hx
  | infinite _ => exact Set.mem_univ _

end NumberField.Adeles

namespace NumberField.Adeles

/--
[infPlace_norm_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma infPlace_norm_algebraMap
  [Field K]
  [NumberField K]
  {wi : InfinitePlace K}
  {x : K} :
-- imply
  ‖algebraMap K wi.Completion x‖ = wi.1 x := by
-- proof
  change ‖(↑((WithAbs.equiv wi.1).symm x) :
    UniformSpace.Completion (WithAbs wi.1))‖ = _
  rw [UniformSpace.Completion.norm_coe]; rfl

end NumberField.Adeles

namespace NumberField.Adeles

/--
[infPlace_denseRange_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
lemma infPlace_denseRange_algebraMap
  [Field K]
  [NumberField K]
  {wi : InfinitePlace K} :
-- imply
  DenseRange (algebraMap K wi.Completion) := by
-- proof
  suffices h : DenseRange (UniformSpace.Completion.coe' ∘
    (WithAbs.equiv wi.1).symm : K → UniformSpace.Completion (WithAbs wi.1)) from h
  exact DenseRange.comp
    (@UniformSpace.Completion.denseRange_coe (WithAbs wi.1) _)
    ((WithAbs.equiv wi.1).symm.surjective.denseRange)
    (UniformSpace.Completion.continuous_coe _)
set_option maxHeartbeats 999999 in

end NumberField.Adeles

/--
[adicCompletion_finite_residueField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
private lemma adicCompletion_finite_residueField_eq
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
-- proof
  apply NumberField.Adeles.adicCompletion_finite_residueField K v

/--
[isCompact_adicCompletionIntegers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
private lemma isCompact_adicCompletionIntegers_eq
  [Field K]
  [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
-- proof
  apply NumberField.Adeles.isCompact_adicCompletionIntegers v

/--
[localBaseChangeMap_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
private lemma localBaseChangeMap_continuous_eq
  [Field K]
  [NumberField K]
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {w : HeightOneSpectrum (𝓞 L)} :
-- imply
  Continuous (localBaseChangeMap K L w) := by
-- proof
  apply NumberField.Adeles.localBaseChangeMap_continuous K L w

/--
[baseChangeAtPrime_mem_integers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
private lemma baseChangeAtPrime_mem_integers_eq
  [Field K]
  [NumberField K]
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {w : HeightOneSpectrum (𝓞 L)}
  {x : (primeBelow K L w).adicCompletion K}
-- given
  (hx : x ∈ (primeBelow K L w).adicCompletionIntegers K) :
-- imply
  (baseChangeAtPrime K L w) x ∈ w.adicCompletionIntegers L := by
-- proof
  apply NumberField.Adeles.baseChangeAtPrime_mem_integers K L w x hx

/--
[baseChange_restricted_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
private lemma baseChange_restricted_condition_eq
  [Field K]
  [NumberField K]
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {a : FiniteAdeleRing (𝓞 K) K} :
-- imply
  ∀ᶠ (w : HeightOneSpectrum (𝓞 L)) in Filter.cofinite, (baseChangeAtPrime K L w) (a (primeBelow K L w)) ∈ ↑(w.adicCompletionIntegers L) := by
-- proof
  apply NumberField.Adeles.baseChange_restricted_condition K L a

/--
[baseChange_commutes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean)
-/
@[path]
private lemma baseChange_commutes_eq
  [Field K]
  [NumberField K]
  {K L : Type*}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  {k : K} :
-- imply
  (RestrictedProduct.mk (fun w => (baseChangeAtPrime K L w) ((algebraMap K (FiniteAdeleRing (𝓞 K) K) k) (primeBelow K L w))) (baseChange_restricted_condition K L (algebraMap K (FiniteAdeleRing (𝓞 K) K) k))) = algebraMap K (FiniteAdeleRing (𝓞 L) L) k := by
-- proof
  apply NumberField.Adeles.baseChange_commutes K L k


-- created on 2026-10-23
