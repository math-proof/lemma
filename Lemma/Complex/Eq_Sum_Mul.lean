import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.CompactMeasures
open Filter Topology Classical
open scoped TensorProduct











/--
[linear_func_decomp_pi_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma linear_func_decomp_pi_abstract
  [Fintype ι]
  [DecidableEq ι]
-- given
  (l : (ι → ℂ) →ₗ[ℂ] ℂ)
  (w : ι → ℂ) :
-- imply
  l w = ∑ i : ι, l (Function.update 0 i 1) * w i := by
-- proof
  conv_lhs => rw [show w = ∑ i : ι, w i • Function.update (0 : ι → ℂ) i 1 from by
    ext j; simp [Finset.sum_apply, Function.update, Finset.mem_univ]]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul, mul_comm]

/--
[evalPairing_linearCombination_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma evalPairing_linearCombination_dirac
  {X : Type*}
  [TopologicalSpace X]
  [AddCommGroup MX]
  [Module ℂ MX]
  [TopologicalSpace MX]
  [inst : CompactlySupportedMeasureSpace X MX]
  {c : Finsupp X ℂ}
  {f : (ContinuousMap X ℂ)} :
-- imply
  inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f = c.sum (fun x a => a * f x) := by
-- proof
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, inst.evalPairing_dirac]

/--
[abstract_match_on_finset_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma abstract_match_on_finset_restricted
  {X : Type*}
  [TopologicalSpace X]
  [AddCommGroup MX]
  [Module ℂ MX]
  [TopologicalSpace MX]
  [inst : CompactlySupportedMeasureSpace X MX]
-- given
  (μ : MX)
  (K : Set X)
  (hK : ∀ (f : (ContinuousMap X ℂ)), (∀ x ∈ K, f x = 0) → inst.evalPairing μ f = 0)
  (I : Finset (ContinuousMap X ℂ)) :
-- imply
  ∃ c : Finsupp X ℂ, (c.support : Set X) ⊆ K ∧ ∀ f ∈ I, inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f = inst.evalPairing μ f := by
-- proof
  let ι := (I : Set (ContinuousMap X ℂ)).Elem
  let φ : K → (ι → ℂ) := fun x i => (i : (ContinuousMap X ℂ)) x.1
  let v : ι → ℂ := fun i => inst.evalPairing μ (i : (ContinuousMap X ℂ))
  have h_span : v ∈ Submodule.span ℂ (Set.range φ) := by
    rw [Submodule.mem_span]; intro p hp; by_contra hv
    obtain ⟨l, hl_v, hl_p⟩ := Submodule.exists_le_ker_of_notMem hv
    have hl_φ : ∀ x : K, l (φ x) = 0 :=
      fun x => LinearMap.mem_ker.mp (hl_p (hp ⟨x, rfl⟩))
    have key_zero : ∀ x' ∈ K,
      ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * ((↑i : (ContinuousMap X ℂ)) x') = 0 := by
      intro x' hx'
      rw [← linear_func_decomp_pi_abstract l (φ ⟨x', hx'⟩)]
      exact hl_φ ⟨x', hx'⟩
    have g_zero_on_K : ∀ x' ∈ K,
      (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : (ContinuousMap X ℂ))) x' = 0 := by
      intro x' hx'
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact key_zero x' hx'
    apply hl_v; rw [linear_func_decomp_pi_abstract l v]
    have : ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * inst.evalPairing μ (↑i : (ContinuousMap X ℂ)) =
      inst.evalPairing μ (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : (ContinuousMap X ℂ))) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    exact hK _ g_zero_on_K
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h_span
  obtain ⟨c_sub, hc_sub⟩ := h_span
  let c : Finsupp X ℂ := c_sub.mapDomain Subtype.val
  refine ⟨c, ?_, ?_⟩
  · intro x hx
    have h1 := Finsupp.mapDomain_support (f := Subtype.val) (s := c_sub)
    have h2 : x ∈ Finset.image Subtype.val c_sub.support := h1 hx
    rw [Finset.mem_image] at h2
    obtain ⟨k, _, rfl⟩ := h2
    exact k.2
  · intro f hf
    rw [evalPairing_linearCombination_dirac]
    have hci : (c_sub.sum fun x a => a • φ x) ⟨f, hf⟩ = v ⟨f, hf⟩ := by rw [hc_sub]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hci
    have hsum : (Finsupp.mapDomain Subtype.val c_sub).sum (fun x a => a * f x) =
      c_sub.sum (fun k a => a * f k.1) :=
      Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)
    simp only [Finsupp.sum] at hsum ⊢
    rwa [hsum]

/--
[CompactlySupportedMeasureSpace.supported_in_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma CompactlySupportedMeasureSpace.supported_in_compact
  {X : Type*}
  [TopologicalSpace X]
  [AddCommGroup MX]
  [Module ℂ MX]
  [TopologicalSpace MX]
  [inst : CompactlySupportedMeasureSpace X MX]
  {μ : MX} :
-- imply
  ∃ K : Set X, IsCompact K ∧ μ ∈ closure ((Finsupp.linearCombination ℂ (CompactlySupportedMeasureSpace.dirac (X := X) (MX := MX))) '' { f : Finsupp X ℂ | (f.support : Set X) ⊆ K }) := by
-- proof
  obtain ⟨K, hKc, hK⟩ := inst.hasCompactSupport μ
  refine ⟨K, hKc, ?_⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [inst.topology_eq_initial] at hU
  rw [Filter.mem_iInf] at hU
  obtain ⟨J_set, hJ_finite, V, hV_mem, hV_eq⟩ := hU
  let J : Finset (ContinuousMap X ℂ) := hJ_finite.toFinset
  obtain ⟨c, hc_supp, hc_match⟩ := abstract_match_on_finset_restricted μ K hK J
  refine ⟨Finsupp.linearCombination ℂ inst.dirac c, ?_, ⟨c, hc_supp, rfl⟩⟩
  rw [hV_eq]
  simp only [Set.mem_iInter]
  intro ⟨f, hf⟩
  have hVf := hV_mem ⟨f, hf⟩
  rw [Filter.mem_comap] at hVf
  obtain ⟨W, hW_nhds, hW_sub⟩ := hVf
  apply hW_sub
  show inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f ∈ W
  have heq : inst.evalPairing (Finsupp.linearCombination ℂ inst.dirac c) f =
    inst.evalPairing μ f :=
    hc_match f (hJ_finite.mem_toFinset.mpr hf)
  rw [heq]
  exact mem_of_mem_nhds hW_nhds

/--
[linear_func_decomp_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma linear_func_decomp_pi
  [Fintype ι]
  [DecidableEq ι]
-- given
  (l : (ι → ℂ) →ₗ[ℂ] ℂ)
  (w : ι → ℂ) :
-- imply
  l w = ∑ i : ι, l (Function.update 0 i 1) * w i := by
-- proof
  conv_lhs => rw [show w = ∑ i : ι, w i • Function.update (0 : ι → ℂ) i 1 from by
    ext j; simp [Finset.sum_apply, Function.update, Finset.mem_univ]]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul, mul_comm]

/--
[concreteDiracEmbed_apply_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma concreteDiracEmbed_apply_sum
  {X : Type*}
  [TopologicalSpace X]
-- given
  (c : Finsupp X ℂ)
  (f : (ContinuousMap X ℂ)) :
-- imply
  (concreteDiracEmbed X c) f = ∑ x ∈ c.support, c x * f x := by
-- proof
  simp only [concreteDiracEmbed, Finsupp.linearCombination_apply, Finsupp.sum]
  have : IsZeroApply (WeakDual ℂ (ContinuousMap X ℂ)) (ContinuousMap X ℂ) ℂ :=
    inferInstanceAs (IsZeroApply (ContinuousLinearMap (RingHom.id ℂ) (ContinuousMap X ℂ) ℂ) (ContinuousMap X ℂ) ℂ)
  have : IsAddApply (WeakDual ℂ (ContinuousMap X ℂ)) (ContinuousMap X ℂ) ℂ :=
    inferInstanceAs (IsAddApply (ContinuousLinearMap (RingHom.id ℂ) (ContinuousMap X ℂ) ℂ) (ContinuousMap X ℂ) ℂ)
  rw [sum_apply]
  change ∑ i ∈ c.support, (c i • ContinuousMap.evalCLM ℂ i) f =
    ∑ x ∈ c.support, c x * f x
  simp [ContinuousMap.evalCLM_apply, smul_eq_mul]

/--
[concreteDiracEmbed_match_on_finset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma concreteDiracEmbed_match_on_finset
  {X : Type*}
  [TopologicalSpace X]
-- given
  (μ : WeakDual ℂ (ContinuousMap X ℂ))
  (I : Finset (ContinuousMap X ℂ)) :
-- imply
  ∃ c : Finsupp X ℂ, ∀ f ∈ I, (concreteDiracEmbed X c) f = μ f := by
-- proof
  let ι := (I : Set (ContinuousMap X ℂ)).Elem
  let φ : X → (ι → ℂ) := fun x i => (i : (ContinuousMap X ℂ)) x
  let v : ι → ℂ := fun i => μ (i : (ContinuousMap X ℂ))
  have h_span : v ∈ Submodule.span ℂ (Set.range φ) := by
    rw [Submodule.mem_span]; intro p hp; by_contra hv
    obtain ⟨l, hl_v, hl_p⟩ := Submodule.exists_le_ker_of_notMem hv
    have hl_φ : ∀ x : X, l (φ x) = 0 :=
      fun x => LinearMap.mem_ker.mp (hl_p (hp ⟨x, rfl⟩))
    have key_zero : ∀ x' : X,
      ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * ((↑i : (ContinuousMap X ℂ)) x') = 0 := by
      intro x'; rw [← linear_func_decomp_pi l (φ x')]; exact hl_φ x'
    have g_zero : (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : (ContinuousMap X ℂ))) = 0 := by
      ext x'; simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, ContinuousMap.zero_apply]; exact key_zero x'
    apply hl_v; rw [linear_func_decomp_pi l v]
    have : ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * μ (↑i : (ContinuousMap X ℂ)) =
      μ (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : (ContinuousMap X ℂ))) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [this, g_zero, map_zero]
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h_span
  obtain ⟨c, hc⟩ := h_span; use c; intro f hf
  have hci : (c.sum fun x a => a • φ x) ⟨f, hf⟩ = v ⟨f, hf⟩ := by rw [hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hci
  rw [concreteDiracEmbed_apply_sum]; exact hci

/--
[concreteDiracEmbed_match_on_finset_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma concreteDiracEmbed_match_on_finset_restricted
  {X : Type*}
  [TopologicalSpace X]
-- given
  (μ : WeakDual ℂ (ContinuousMap X ℂ))
  (K : Set X)
  (hK : ∀ (f : (ContinuousMap X ℂ)), (∀ x ∈ K, f x = 0) → μ f = 0)
  (I : Finset (ContinuousMap X ℂ)) :
-- imply
  ∃ c : Finsupp X ℂ, (c.support : Set X) ⊆ K ∧ ∀ f ∈ I, (concreteDiracEmbed X c) f = μ f := by
-- proof
  let ι := (I : Set (ContinuousMap X ℂ)).Elem
  let φ : K → (ι → ℂ) := fun x i => (i : (ContinuousMap X ℂ)) x.1
  let v : ι → ℂ := fun i => μ (i : (ContinuousMap X ℂ))
  have h_span : v ∈ Submodule.span ℂ (Set.range φ) := by
    rw [Submodule.mem_span]; intro p hp; by_contra hv
    obtain ⟨l, hl_v, hl_p⟩ := Submodule.exists_le_ker_of_notMem hv
    have hl_φ : ∀ x : K, l (φ x) = 0 :=
      fun x => LinearMap.mem_ker.mp (hl_p (hp ⟨x, rfl⟩))
    have key_zero : ∀ x' ∈ K,
      ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * ((↑i : (ContinuousMap X ℂ)) x') = 0 := by
      intro x' hx'
      rw [← linear_func_decomp_pi l (φ ⟨x', hx'⟩)]
      exact hl_φ ⟨x', hx'⟩
    have g_zero_on_K : ∀ x' ∈ K,
      (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : (ContinuousMap X ℂ))) x' = 0 := by
      intro x' hx'
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact key_zero x' hx'
    apply hl_v; rw [linear_func_decomp_pi l v]
    have : ∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) * μ (↑i : (ContinuousMap X ℂ)) =
      μ (∑ i : ι, l (Function.update (0 : ι → ℂ) i 1) • (↑i : (ContinuousMap X ℂ))) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [this]
    exact hK _ g_zero_on_K
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h_span
  obtain ⟨c_sub, hc_sub⟩ := h_span
  let c : Finsupp X ℂ := c_sub.mapDomain Subtype.val
  refine ⟨c, ?_, ?_⟩
  ·
    intro x hx
    have h1 := Finsupp.mapDomain_support (f := Subtype.val) (s := c_sub)
    have h2 : x ∈ Finset.image Subtype.val c_sub.support := h1 hx
    rw [Finset.mem_image] at h2
    obtain ⟨k, _, rfl⟩ := h2
    exact k.2
  ·
    intro f hf
    rw [concreteDiracEmbed_apply_sum]
    have hci : (c_sub.sum fun x a => a • φ x) ⟨f, hf⟩ = v ⟨f, hf⟩ := by rw [hc_sub]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hci
    have hsum : (Finsupp.mapDomain Subtype.val c_sub).sum (fun x a => a * f x) =
      c_sub.sum (fun k a => a * f k.1) :=
      Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)
    simp only [Finsupp.sum] at hsum ⊢
    rwa [hsum]

/--
[concreteDiracEmbed_range_dense_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma concreteDiracEmbed_range_dense_ax
  {X : Type*}
  [TopologicalSpace X]
-- given
  (μ : WeakDual ℂ (ContinuousMap X ℂ)) :
-- imply
  μ ∈ closure (Set.range (concreteDiracEmbed X)) := by
-- proof
  rw [mem_closure_iff_nhds]
  intro U hU
  have hnhds : 𝓝 μ =
      Filter.comap (fun ν : WeakDual ℂ (ContinuousMap X ℂ) => (fun f : (ContinuousMap X ℂ) => ν f))
        (𝓝 (fun f : (ContinuousMap X ℂ) => μ f)) :=
    nhds_induced (fun ν : WeakDual ℂ (ContinuousMap X ℂ) => (fun f : (ContinuousMap X ℂ) => ν f)) μ
  rw [hnhds] at hU
  obtain ⟨V, hV, hVU⟩ := (Filter.mem_comap).1 hU
  have hVpi : V ∈ 𝓝 (fun f : (ContinuousMap X ℂ) => μ f) := hV
  rw [nhds_pi] at hVpi
  obtain ⟨J, t, ht, htV⟩ := Filter.mem_pi'.1 hVpi
  obtain ⟨c, hc⟩ := concreteDiracEmbed_match_on_finset μ J
  refine ⟨concreteDiracEmbed X c, ?_, ⟨c, rfl⟩⟩
  apply hVU
  apply htV
  intro f hf
  dsimp only
  exact (hc f hf) ▸ mem_of_mem_nhds (ht f)

/--
[finitelySupportedMeasures_dense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma finitelySupportedMeasures_dense
-- given
  (X : Type*)
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X] :
-- imply
  Dense (Set.range (concreteDiracEmbed X)) := by
-- proof
  rw [dense_iff_closure_eq]
  ext x
  simp only [Set.mem_univ, iff_true]
  exact concreteDiracEmbed_range_dense_ax x

/--
[lemma_3_4_dense_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma lemma_3_4_dense_concrete
-- given
  (X : Type*)
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X] :
-- imply
  Dense (Set.range (concreteDiracEmbed X)) :=
-- proof
  finitelySupportedMeasures_dense X

/--
[boxtimesAtomic_single_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma boxtimesAtomic_single_single
  {X Y : Type*}
  {x : X}
  {y : Y}
  {a b : ℂ} :
-- imply
  boxtimesAtomic X Y (Finsupp.single x a) (Finsupp.single y b) = Finsupp.single (x, y) (a * b) := by
-- proof
  simp [boxtimesAtomic, LinearMap.compr₂, finsuppTensorFinsupp']

/--
[boxtimes_extension_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompactMeasures.lean)
-/
@[path]
private lemma boxtimes_extension_unique
  {X Y : Type*}
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  [TopologicalSpace Y]
  [LocallyCompactSpace Y]
  [SecondCountableTopology Y]
  [T2Space Y]
  {bt₁ bt₂ : WeakDual ℂ (ContinuousMap X ℂ) →ₗ[ℂ] WeakDual ℂ (ContinuousMap Y ℂ) →ₗ[ℂ] WeakDual ℂ (ContinuousMap (X × Y) ℂ)}
-- given
  (hext₁ : ∀ (μ : Finsupp X ℂ) (ν : Finsupp Y ℂ), bt₁ (concreteDiracEmbed X μ) (concreteDiracEmbed Y ν) = concreteDiracEmbed (X × Y) (boxtimesAtomic X Y μ ν))
  (hext₂ : ∀ (μ : Finsupp X ℂ) (ν : Finsupp Y ℂ), bt₂ (concreteDiracEmbed X μ) (concreteDiracEmbed Y ν) = concreteDiracEmbed (X × Y) (boxtimesAtomic X Y μ ν))
  (hcont₁_l : ∀ (ν : WeakDual ℂ (ContinuousMap Y ℂ)), Continuous (fun μ => bt₁ μ ν))
  (hcont₁_r : ∀ (μ : WeakDual ℂ (ContinuousMap X ℂ)), Continuous (fun ν => bt₁ μ ν))
  (hcont₂_l : ∀ (ν : WeakDual ℂ (ContinuousMap Y ℂ)), Continuous (fun μ => bt₂ μ ν))
  (hcont₂_r : ∀ (μ : WeakDual ℂ (ContinuousMap X ℂ)), Continuous (fun ν => bt₂ μ ν)) :
-- imply
  bt₁ = bt₂ := by
-- proof
  ext μ ν
  have step1 : ∀ (ν₀ : Finsupp Y ℂ) (μ : WeakDual ℂ (ContinuousMap X ℂ)),
    bt₁ μ (concreteDiracEmbed Y ν₀) = bt₂ μ (concreteDiracEmbed Y ν₀) := by
    intro ν₀
    have heq : Set.EqOn
      (fun μ => bt₁ μ (concreteDiracEmbed Y ν₀))
      (fun μ => bt₂ μ (concreteDiracEmbed Y ν₀))
      (Set.range (concreteDiracEmbed X)) := by
      rintro _ ⟨μ₀, rfl⟩
      dsimp only
      rw [hext₁ μ₀ ν₀, hext₂ μ₀ ν₀]
    exact fun μ => congr_fun (Continuous.ext_on
      (lemma_3_4_dense_concrete X)
      (hcont₁_l _) (hcont₂_l _) heq) μ
  have heq : Set.EqOn
    (fun ν => bt₁ μ ν)
    (fun ν => bt₂ μ ν)
    (Set.range (concreteDiracEmbed Y)) := by
    rintro _ ⟨ν₀, rfl⟩
    dsimp only
    exact step1 ν₀ μ
  exact congr_fun (Continuous.ext_on
    (lemma_3_4_dense_concrete Y)
    (hcont₁_r μ) (hcont₂_r μ) heq) ν


-- created on 2026-10-23
-- updated on 2026-10-24
