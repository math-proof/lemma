import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Dual
/-!
# Strong linear programming duality

A feasible bounded-above primal `max { c ⬝ᵥ x | x ≥ 0, A *ᵥ x ≤ b }` attains
its supremum, and there is a dual-feasible `y ≥ 0` with `c ≤ Aᵀ *ᵥ y` and
equal objective value `c ⬝ᵥ x = b ⬝ᵥ y`.

Informal source: George B. Dantzig, *Linear Programming and Extensions*,
Princeton University Press, 1963, strong duality theorem.
-/


namespace Convex.LPDuality

open scoped Topology Matrix

open Finset Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in
/-- Elimination step: a relation kills one generator. -/
lemma hull_elim {S : Finset E} {c : E →₀ ℝ} (hc : ∀ i, 0 ≤ c i)
    (hsupp : c.support ⊆ ↑S) {d : E →₀ ℝ} (hd : d ≠ 0)
    (hdsupp : d.support ⊆ ↑S)
    (hrel : Finsupp.linearCombination ℝ id d = 0)
    {y : E} (hy : Finsupp.linearCombination ℝ id c = y) :
    ∃ j ∈ S, y ∈ PointedCone.hull ℝ (↑(S.erase j) : Set E) := by
  have step : ∀ {d : E →₀ ℝ}, d.support ⊆ ↑S →
      Finsupp.linearCombination ℝ id d = 0 →
      (S.filter (fun i => 0 < d i)).Nonempty →
      ∃ j ∈ S, y ∈ PointedCone.hull ℝ (↑(S.erase j) : Set E) := by
    intro d hdsupp hrel ⟨j, hjP⟩
    obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image
      (S.filter (fun i => 0 < d i)) (fun i => c i / d i) ⟨j, hjP⟩
    rw [Finset.mem_filter] at hjP
    obtain ⟨hjS, hdj⟩ := hjP
    set t := c j / d j with ht
    have hdj' : d j ≠ 0 := ne_of_gt hdj
    have htnonneg : 0 ≤ t := div_nonneg (hc j) hdj.le
    -- new weights
    set c' : E →₀ ℝ := c - t • d with hc'def
    have hci : ∀ i, c' i = c i - t * d i := fun i => by
      simp [hc'def, Finsupp.sub_apply, Finsupp.smul_apply]
    have hc' : ∀ i, 0 ≤ c' i := by
      intro i
      rw [hci]
      by_cases hSi : i ∈ S
      · by_cases hdi : 0 < d i
        · have hmem : i ∈ S.filter (fun i => 0 < d i) :=
            Finset.mem_filter.mpr ⟨hSi, hdi⟩
          have hle : t ≤ c i / d i := hjmin i hmem
          have h := (le_div_iff₀ hdi).mp hle
          linarith
        · push Not at hdi
          have h := mul_nonpos_of_nonneg_of_nonpos htnonneg hdi
          have := hc i
          linarith
      · have hcz : c i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hsupp h))
        have hdz : d i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hdsupp h))
        rw [hcz, hdz, mul_zero, sub_zero]
    have hsupp' : c'.support ⊆ ↑(S.erase j) := by
      intro i hi
      rw [Finset.mem_erase]
      have hne : c' i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hiS : i ∈ S := by
        by_contra hSi
        have hcz : c i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hsupp h))
        have hdz : d i = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hSi (hdsupp h))
        rw [hci, hcz, hdz, mul_zero, sub_zero] at hne
        exact hne rfl
      refine ⟨?_, hiS⟩
      intro hij
      apply hne
      rw [hci, hij, ht, div_mul_cancel₀ _ hdj', sub_self]
    have hcomb' : Finsupp.linearCombination ℝ id c' = y := by
      rw [hc'def, map_sub, map_smul, hrel, smul_zero, sub_zero]
      exact hy
    refine ⟨j, hjS, PointedCone.mem_hull_set.mpr ⟨c', hsupp', hc', ?_⟩⟩
    simpa [Finsupp.linearCombination_apply] using hcomb'
  -- sign choice
  obtain ⟨i, hiS, hdi⟩ : ∃ i ∈ S, d i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hd
    ext i
    by_cases hiS : i ∈ S
    · simp [hcon i hiS]
    · have h : i ∉ d.support :=
        fun hm => hiS (hdsupp hm)
      rw [Finsupp.notMem_support_iff.mp h]
      rfl
  by_cases hpos : 0 < d i
  · exact step hdsupp hrel ⟨i, Finset.mem_filter.mpr ⟨hiS, hpos⟩⟩
  · push Not at hpos
    have hneg : 0 < (-d) i := by
      rw [Finsupp.neg_apply]
      have : d i < 0 := lt_of_le_of_ne hpos hdi
      linarith
    have hdsupp' : (-d).support ⊆ ↑S := by
      rw [Finsupp.support_neg]
      exact hdsupp
    have hrel' : Finsupp.linearCombination ℝ id (-d) = 0 := by
      rw [map_neg, hrel, neg_zero]
    exact step hdsupp' hrel' ⟨i, Finset.mem_filter.mpr ⟨hiS, hneg⟩⟩

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- Every cone element has a representation over an independent subset. -/
lemma hull_indep_repr {S : Finset E} {y : E}
    (hy : y ∈ PointedCone.hull ℝ (↑S : Set E)) :
    ∃ T : Finset E, T ⊆ S ∧ LinearIndependent ℝ ((↑) : T → E) ∧
      y ∈ PointedCone.hull ℝ (↑T : Set E) := by
  classical
  induction S using Finset.strongInduction with
  | H S IH =>
    by_cases hindep : LinearIndependent ℝ ((↑) : S → E)
    · exact ⟨S, Finset.Subset.rfl, hindep, hy⟩
    · rw [linearIndependent_iff] at hindep
      push Not at hindep
      obtain ⟨l, hl0, hln⟩ := hindep
      set e : ↥S ↪ E := Function.Embedding.subtype (· ∈ S)
      set d : E →₀ ℝ := l.embDomain e with hddef
      have hdsupp : d.support ⊆ ↑S := by
        intro i hi
        rw [hddef, Finsupp.support_embDomain] at hi
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
        exact a.property
      have hd : d ≠ 0 := by
        rw [hddef, Ne, Finsupp.embDomain_eq_zero]
        exact hln
      have hrel : Finsupp.linearCombination ℝ id d = 0 := by
        rw [hddef, Finsupp.linearCombination_embDomain]
        have : (id ∘ e : ↥S → E) = ((↑) : ↥S → E) := rfl
        rw [this]
        exact hl0
      obtain ⟨c, hsupp, hc, hcomb⟩ := PointedCone.mem_hull_set.mp hy
      have hcomb' : Finsupp.linearCombination ℝ id c = y := by
        simpa [Finsupp.linearCombination_apply] using hcomb
      obtain ⟨j, hjS, hy'⟩ := hull_elim hc hsupp hd hdsupp hrel hcomb'
      obtain ⟨T, hTS, hindepT, hyT⟩ :=
        IH (S.erase j) (Finset.erase_ssubset hjS) hy'
      exact ⟨T, hTS.trans (Finset.erase_subset _ _), hindepT, hyT⟩

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- Finitely generated cones are closed. -/
lemma isClosed_hull_finset (S : Finset E) :
    IsClosed (PointedCone.hull ℝ (↑S : Set E) : Set E) := by
  classical
  apply IsSeqClosed.isClosed
  intro f x hfs hf
  have hrep : ∀ n, ∃ T : Finset E, T ⊆ S ∧
      LinearIndependent ℝ ((↑) : T → E) ∧
        f n ∈ PointedCone.hull ℝ (↑T : Set E) :=
    fun n => hull_indep_repr (hfs n)
  choose T hTS hindep hmemT using hrep
  set g : ℕ → ↥(S.powerset) :=
    fun n => ⟨T n, Finset.mem_powerset.mpr (hTS n)⟩ with hgdef
  obtain ⟨T₀, hfib⟩ := Finite.exists_infinite_fiber g
  have hfib' : {n : ℕ | T n = (T₀ : Finset E)}.Infinite := by
    have heq : g ⁻¹' {T₀} = {n : ℕ | T n = (T₀ : Finset E)} := by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      rw [Subtype.ext_iff]
    rw [← heq]
    exact Set.infinite_coe_iff.mp hfib
  set e := @Infinite.natEmbedding _ hfib'.to_subtype with hedef
  set φ : ℕ → ℕ :=
    fun n => ((e n : ↥{n : ℕ | T n = (T₀ : Finset E)}) : ℕ) with hφdef
  have hφinj : Function.Injective φ :=
    Subtype.val_injective.comp e.injective
  have hφtop : Tendsto φ atTop atTop := hφinj.nat_tendsto_atTop
  have hφmem : ∀ n, T (φ n) = (T₀ : Finset E) := fun n => (e n).property
  have hflim : Tendsto (f ∘ φ) atTop (𝓝 x) := hf.comp hφtop
  have hmemφ : ∀ n, (f ∘ φ) n ∈
      PointedCone.hull ℝ (↑(T₀ : Finset E) : Set E) := by
    intro n
    rw [← hφmem n]
    exact hmemT (φ n)
  have hT0indep : LinearIndependent ℝ ((↑) : ↥(T₀ : Finset E) → E) := by
    have h := hindep (φ 0)
    rwa [hφmem 0] at h
  set G : (↥(T₀ : Finset E) → ℝ) →ₗ[ℝ] E :=
    ∑ i : ↥(T₀ : Finset E), (LinearMap.proj i).smulRight (i : E) with hGdef
  have hGapply : ∀ r : ↥(T₀ : Finset E) → ℝ,
      G r = ∑ i : ↥(T₀ : Finset E), r i • (i : E) := by
    intro r
    simp [hGdef, LinearMap.sum_apply]
  have hGker : ∀ r : ↥(T₀ : Finset E) → ℝ, G r = 0 → r = 0 := by
    intro r hr
    have hsum : (∑ i : ↥(T₀ : Finset E), r i • ((i : ↥(T₀ : Finset E)) : E)) = 0 := by
      rw [← hGapply]
      exact hr
    have h0 := (linearIndependent_iff.mp hT0indep)
      (Finsupp.onFinset Finset.univ r (fun a _ => Finset.mem_univ a))
      (by rw [Finsupp.linearCombination_onFinset]; exact hsum)
    funext i
    have hci := congr_fun (congr_arg DFunLike.coe h0) i
    simpa using hci
  have hGinj : Function.Injective G := by
    intro r₁ r₂ h
    have h0 : r₁ - r₂ = 0 := hGker _ (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp h0
  have hcrep : ∀ n, ∃ r : ↥(T₀ : Finset E) → ℝ,
      (∀ i, 0 ≤ r i) ∧ G r = (f ∘ φ) n := by
    intro n
    obtain ⟨c, hsupp, hc, hcomb⟩ := PointedCone.mem_hull_set.mp (hmemφ n)
    refine ⟨fun i => c (i : E), fun i => hc _, ?_⟩
    have hsum : Finsupp.linearCombination ℝ id c =
        ∑ i : ↥(T₀ : Finset E), c (i : E) • ((i : ↥(T₀ : Finset E)) : E) := by
      have hfin : Finsupp.linearCombination ℝ id c =
          ∑ i ∈ (T₀ : Finset E), c i • (i : E) := by
        rw [Finsupp.linearCombination_apply]
        exact Finsupp.sum_of_support_subset c hsupp _ (fun i _ => by simp)
      rw [hfin, ← Finset.sum_attach]
      rfl
    rw [hGapply]
    rw [← hsum]
    simpa [Finsupp.linearCombination_apply] using hcomb
  choose r hrnonneg hrG using hcrep
  set RG := LinearMap.range G with hRGdef
  have hRGclosed : IsClosed (↑RG : Set E) :=
    Submodule.closed_of_finiteDimensional RG
  have hmemRG : ∀ n, (f ∘ φ) n ∈ RG := fun n => ⟨r n, hrG n⟩
  have hyRG : x ∈ RG :=
    hRGclosed.mem_of_tendsto hflim (Filter.Eventually.of_forall hmemRG)
  have hyRGmem := hyRG
  obtain ⟨rstar, hrstar⟩ := hyRG
  have hHcont : Continuous
      ((LinearEquiv.ofInjective G hGinj).symm.toLinearMap) :=
    LinearMap.continuous_of_finiteDimensional _
  have hsub : Tendsto (fun n => (⟨(f ∘ φ) n, hmemRG n⟩ : RG)) atTop
      (𝓝 ⟨x, hyRGmem⟩) :=
    tendsto_subtype_rng.mpr hflim
  have hrlim : Tendsto r atTop (𝓝 rstar) := by
    have h1 : Tendsto
        (fun n => (LinearEquiv.ofInjective G hGinj).symm.toLinearMap
          (⟨(f ∘ φ) n, hmemRG n⟩ : RG)) atTop
        (𝓝 ((LinearEquiv.ofInjective G hGinj).symm.toLinearMap ⟨x, hyRGmem⟩)) :=
      (hHcont.tendsto _).comp hsub
    have h2 : (fun n => (LinearEquiv.ofInjective G hGinj).symm.toLinearMap
        (⟨(f ∘ φ) n, hmemRG n⟩ : RG)) = r := by
      funext n
      have hmem : (⟨(f ∘ φ) n, hmemRG n⟩ : RG)
          = (LinearEquiv.ofInjective G hGinj) (r n) :=
        Subtype.ext (hrG n).symm
      rw [hmem]
      change (LinearEquiv.ofInjective G hGinj).symm
        ((LinearEquiv.ofInjective G hGinj) (r n)) = r n
      exact LinearEquiv.symm_apply_apply _ _
    have h3 : (LinearEquiv.ofInjective G hGinj).symm.toLinearMap ⟨x, hyRGmem⟩
        = rstar := by
      have hmem : (⟨x, hyRGmem⟩ : RG)
          = (LinearEquiv.ofInjective G hGinj) rstar :=
        Subtype.ext hrstar.symm
      rw [hmem]
      change (LinearEquiv.ofInjective G hGinj).symm
        ((LinearEquiv.ofInjective G hGinj) rstar) = rstar
      exact LinearEquiv.symm_apply_apply _ _
    rw [h2, h3] at h1
    exact h1
  have hrstar_nonneg : ∀ i, 0 ≤ rstar i := by
    intro i
    apply ge_of_tendsto (tendsto_pi_nhds.mp hrlim i)
    filter_upwards with n
    exact hrnonneg n i
  have hxG : G rstar = x := by
    have h1 : Tendsto (G ∘ r) atTop (𝓝 (G rstar)) :=
      ((LinearMap.continuous_of_finiteDimensional G).tendsto _).comp hrlim
    have h2 : (G ∘ r) = (f ∘ φ) := funext (fun n => hrG n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hflim
  have hxrep : x ∈ PointedCone.hull ℝ (↑(T₀ : Finset E) : Set E) := by
    apply PointedCone.mem_hull_set.mpr
    refine ⟨∑ i : ↥(T₀ : Finset E), Finsupp.single (i : E) (rstar i), ?_, ?_, ?_⟩
    · intro j hj
      have hne : (∑ i : ↥(T₀ : Finset E),
          Finsupp.single (i : E) (rstar i)) j ≠ 0 :=
        Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj)
      by_contra hjS
      have hzero : ∀ i : ↥(T₀ : Finset E),
          (Finsupp.single (i : E) (rstar i)) j = 0 := by
        intro i
        apply Finsupp.single_eq_of_ne
        intro hcon
        exact hjS (hcon ▸ i.property)
      have : (∑ i : ↥(T₀ : Finset E), Finsupp.single (i : E) (rstar i)) j = 0 := by
        rw [Finsupp.finsetSum_apply]
        exact Finset.sum_eq_zero (fun i _ => hzero i)
      exact hne this
    · intro j
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_nonneg
      intro i _
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst h
        exact hrstar_nonneg i
      · exact le_rfl
    · change Finsupp.linearCombination ℝ id
          (∑ i : ↥(T₀ : Finset E), Finsupp.single (i : E) (rstar i)) = x
      rw [map_sum]
      simp only [Finsupp.linearCombination_single]
      change (∑ x : ↥(T₀ : Finset E), rstar x • ((x : ↥(T₀ : Finset E)) : E)) = x
      rw [← hGapply, hxG]
  exact Submodule.span_mono
    (Finset.coe_subset.mpr (Finset.mem_powerset.mp T₀.property)) hxrep

end Convex.LPDuality
