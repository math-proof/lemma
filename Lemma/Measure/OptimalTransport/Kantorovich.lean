import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.OptimalTransport.Kantorovich
open MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported ENNReal
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted


namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[isCoupling_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma isCoupling_prod
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
  IsCoupling μ ν (μ.prod ν) := by
  refine ⟨?_, ?_⟩
  · have h : ((μ.prod ν).map Prod.fst : ProbabilityMeasure X) = μ :=
    ProbabilityMeasure.map_fst_prod μ ν
    have h2 := congrArg (fun π : ProbabilityMeasure X => (π : Measure X)) h
    rwa [ProbabilityMeasure.toMeasure_map] at h2
  · have h : ((μ.prod ν).map Prod.snd : ProbabilityMeasure Y) = ν :=
    ProbabilityMeasure.map_snd_prod μ ν
    have h2 := congrArg (fun π : ProbabilityMeasure Y => (π : Measure Y)) h
    rwa [ProbabilityMeasure.toMeasure_map] at h2

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[primalValues_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma primalValues_nonempty
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
  (c : X × Y → ℝ) :
  (primalValues μ ν c).Nonempty :=
  ⟨∫ p, c p ∂((μ.prod ν) : Measure (X × Y)),
    μ.prod ν, isCoupling_prod μ ν, rfl⟩

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[dualValues_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma dualValues_nonempty
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
  (c : X × Y → ℝ) (hc : Continuous c) :
  {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
    DualFeasible c φ ψ ∧
    r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}.Nonempty := by
  obtain ⟨p₀, -, hp₀⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  have hmin : ∀ x : X, ∀ y : Y, c p₀ ≤ c (x, y) :=
    fun x y => isMinOn_iff.mp hp₀ (x, y) (Set.mem_univ _)
  refine ⟨c p₀, (fun _ => c p₀ / 2), (fun _ => c p₀ / 2),
    ⟨continuous_const, continuous_const, fun x y => ?_⟩, ?_⟩
  · have h := hmin x y
    change c p₀ / 2 + c p₀ / 2 ≤ c (x, y)
    linarith
  · have h1 : (∫ _ : X, c p₀ / 2 ∂(μ : Measure X)) = c p₀ / 2 := by simp
    have h2 : (∫ _ : Y, c p₀ / 2 ∂(ν : Measure Y)) = c p₀ / 2 := by simp
    rw [h1, h2]
    ring

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[mkBCF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma mkBCF_apply
  {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
  (f : W → ℝ) (hf : Continuous f) (x : W) : mkBCF f hf x = f x :=
  rfl

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[exists_max_attain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma exists_max_attain
  {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
  (f : W →ᵇ ℝ) : ∃ z₀, ∀ z, f z ≤ f z₀ := by
  obtain ⟨z₀, -, hz₀⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.continuousOn
  exact ⟨z₀, fun z => isMaxOn_iff.mp hz₀ z (Set.mem_univ _)⟩

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[PhiLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma PhiLM_apply
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
  (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (z : X × Y) :
  (PhiLM d) z = d.1 z.1 + d.2 z.2 :=
  rfl

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[isOpen_negBCF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma isOpen_negBCF
  {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W] :
  IsOpen {w : W →ᵇ ℝ | ∀ z, w z < 0} := by
  rw [Metric.isOpen_iff]
  intro w hw
  obtain ⟨z₀, hz₀⟩ := exists_max_attain w
  have hneg : w z₀ < 0 := hw z₀
  refine ⟨-(w z₀), by linarith, fun w' hw' => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw'
  intro z
  have h3 : w' z - w z ≤ ‖w' - w‖ := by
    have hnorm := (w' - w).norm_coe_le_norm z
    rw [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] at hnorm
    exact le_trans (le_abs_self _) hnorm
  have h4 : w z ≤ w z₀ := hz₀ z
  linarith

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[convex_negBCF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma convex_negBCF
  {W : Type*} [TopologicalSpace W] :
  Convex ℝ {w : W →ᵇ ℝ | ∀ z, w z < 0} := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab z
  have e : (a • w₁ + b • w₂) z = a * w₁ z + b * w₂ z := by
    rw [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [e]
  have h1 : a * w₁ z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt (hw₁ z))
  have h2 : b * w₂ z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt (hw₂ z))
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    rw [ha0, hb1]
    simp only [zero_mul, one_mul, zero_add]
    exact hw₂ z
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hlt : a * w₁ z < 0 := mul_neg_of_pos_of_neg hapos (hw₁ z)
    linarith

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[sepMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma sepMap_apply
  {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ)
  (p : (W →ᵇ ℝ) × ℝ) (z : W) :
  sepMap cb t p z = p.1 z - cb z - (p.2 - t) := by
  change (p.1 - cb - (p.2 - t) • 1) z = _
  rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply]
  congr 1
  have h1 : (1 : (W →ᵇ ℝ)) z = 1 := rfl
  rw [h1, smul_eq_mul, mul_one]

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[sepMap_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma sepMap_continuous
  {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
  Continuous (sepMap cb t) := by
  have h1 : Continuous (fun p : (W →ᵇ ℝ) × ℝ => p.1 - cb) :=
    continuous_fst.sub continuous_const
  have h2 : Continuous (fun p : (W →ᵇ ℝ) × ℝ => (p.2 - t) • (1 : (W →ᵇ ℝ))) :=
    (continuous_snd.sub continuous_const).smul continuous_const
  have h3 := h1.sub h2
  exact h3

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[sepSet_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma sepSet_mem
  {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ)
  (p : (W →ᵇ ℝ) × ℝ) :
  p ∈ sepSet cb t ↔ ∀ z, p.1 z - cb z - (p.2 - t) < 0 := by
  constructor
  · intro h z
    have h2 := h z
    rwa [sepMap_apply] at h2
  · intro h z
    show (sepMap cb t p) z < 0
    rw [sepMap_apply]
    exact h z

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[isOpen_sepSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma isOpen_sepSet
  {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
  (cb : W →ᵇ ℝ) (t : ℝ) : IsOpen (sepSet cb t) :=
  isOpen_negBCF.preimage (sepMap_continuous cb t)

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[sepMap_affine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma sepMap_affine
  {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ)
  (p q : (W →ᵇ ℝ) × ℝ) (a b : ℝ) (hab : a + b = 1) :
  sepMap cb t (a • p + b • q) = a • sepMap cb t p + b • sepMap cb t q := by
  apply BoundedContinuousFunction.ext
  intro z
  have e1 : ((a • p + b • q).1) z = a • p.1 z + b • q.1 z := rfl
  have e2 : (a • p + b • q).2 = a • p.2 + b • q.2 := rfl
  rw [sepMap_apply, e1, e2, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.smul_apply,
    sepMap_apply, sepMap_apply]
  simp only [smul_eq_mul]
  linear_combination (cb z - t) * hab

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[convex_sepSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma convex_sepSet
  {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
  Convex ℝ (sepSet cb t) := by
  intro p hp q hq a b ha hb hab
  have hp' : sepMap cb t p ∈ {w : W →ᵇ ℝ | ∀ z, w z < 0} := hp
  have hq' : sepMap cb t q ∈ {w : W →ᵇ ℝ | ∀ z, w z < 0} := hq
  have haff := sepMap_affine cb t p q a b hab
  change sepMap cb t (a • p + b • q) ∈ {w : W →ᵇ ℝ | ∀ z, w z < 0}
  rw [haff]
  exact convex_negBCF hp' hq' ha hb hab

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[nonempty_sepSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma nonempty_sepSet
  {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
  (sepSet cb t).Nonempty := by
  refine ⟨(cb - 1, t + 1), ?_⟩
  rw [sepSet_mem]
  intro z
  have e : (cb - 1) z = cb z - 1 := rfl
  rw [e]
  linarith

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[disjoint_graph_sepSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma disjoint_graph_sepSet
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
  (c : X × Y → ℝ) (hc : Continuous c)
  (Dstar ε : ℝ) (hε : 0 < ε)
  (hD : ∀ (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ),
    (∀ z, (PhiLM d) z - c z ≤ m) →
    (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ Dstar) :
  Disjoint (sepSet (mkBCF c hc) (Dstar + ε))
    (↑(graphSub (μ : Measure X) (ν : Measure Y))) := by
  have eprod : ∀ dd, (LinearMap.prod PhiLM (dualValLM (μ : Measure X) (ν : Measure Y))) dd
    = (PhiLM dd, dualValLM (μ : Measure X) (ν : Measure Y) dd) := fun dd => rfl
  rw [Set.disjoint_left]
  rintro p hpU hpmem
  obtain ⟨d, rfl⟩ := hpmem
  rw [eprod] at hpU
  rw [sepSet_mem] at hpU
  have hpU' : ∀ z, (PhiLM d) z - (mkBCF c hc) z
    - ((dualValLM (μ : Measure X) (ν : Measure Y) d) - (Dstar + ε)) < 0 := hpU
  obtain ⟨z₀, hz₀⟩ := exists_max_attain (PhiLM d - mkBCF c hc)
  have hmax : ∀ z, (PhiLM d) z - c z ≤ (PhiLM d) z₀ - c z₀ := by
    intro z
    have h := hz₀ z
    have e : ∀ w : X × Y, (PhiLM d - mkBCF c hc) w = (PhiLM d) w - c w :=
      fun w => rfl
    rwa [e z, e z₀] at h
  have hkey := hD d ((PhiLM d) z₀ - c z₀) hmax
  have hlt := hpU' z₀
  have e0 : (mkBCF c hc) z₀ = c z₀ := rfl
  rw [e0] at hlt
  linarith

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[coupling_of_posFunctional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma coupling_of_posFunctional
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
  (c : X × Y → ℝ) (hc : Continuous c)
  (Dstar ε : ℝ)
  (Pim : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ)
  (hpos : ∀ w, (∀ z, 0 ≤ w z) → 0 ≤ Pim w)
  (hPhi : ∀ d, Pim (PhiLM d) = dualValLM (μ : Measure X) (ν : Measure Y) d)
  (hcost : Pim (mkBCF c hc) ≤ Dstar + ε)
  (hone : Pim 1 = 1) :
  ∃ π : ProbabilityMeasure (X × Y), IsCoupling μ ν π ∧
    (∫ p, c p ∂(π : Measure (X × Y))) ≤ Dstar + ε := by
  have eadd : ∀ g h : C_c(X × Y, ℝ), (g + h).toBoundedContinuousFunction
    = g.toBoundedContinuousFunction + h.toBoundedContinuousFunction := by
    intro g h
    apply BoundedContinuousFunction.ext
    intro z
    rfl
  have esmul : ∀ (a : ℝ) (g : C_c(X × Y, ℝ)), (a • g).toBoundedContinuousFunction
    = a • g.toBoundedContinuousFunction := by
    intro a g
    apply BoundedContinuousFunction.ext
    intro z
    rfl
  let ΛR : C_c(X × Y, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun g => Pim (g.toBoundedContinuousFunction)
      map_add' := fun g h => by
        change Pim ((g + h).toBoundedContinuousFunction)
          = Pim (g.toBoundedContinuousFunction) + Pim (h.toBoundedContinuousFunction)
        rw [eadd, map_add]
      map_smul' := fun a g => by
        change Pim ((a • g).toBoundedContinuousFunction)
          = a • Pim (g.toBoundedContinuousFunction)
        rw [esmul, map_smulₛₗ, RingHom.id_apply]
      monotone' := fun g h hgh => by
        change Pim (g.toBoundedContinuousFunction) ≤ Pim (h.toBoundedContinuousFunction)
        have hle : ∀ z, (g.toBoundedContinuousFunction) z
          ≤ (h.toBoundedContinuousFunction) z :=
          fun z => CompactlySupportedContinuousMap.le_def.mp hgh z
        have hnonneg : 0
          ≤ Pim (h.toBoundedContinuousFunction - g.toBoundedContinuousFunction) :=
          hpos _ (fun z => by
            rw [BoundedContinuousFunction.sub_apply]
            linarith [hle z])
        have hadd : Pim (h.toBoundedContinuousFunction - g.toBoundedContinuousFunction)
          = Pim (h.toBoundedContinuousFunction) - Pim (g.toBoundedContinuousFunction) := by
          rw [map_sub]
        linarith }
  have hΛR : ∀ g : C_c(X × Y, ℝ), ΛR g = Pim (g.toBoundedContinuousFunction) :=
    fun g => rfl
  set πM : Measure (X × Y) := RealRMK.rieszMeasure ΛR with hπM
  set one_cc : C_c(X × Y, ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv 1 with honecc
  have eBCFone : one_cc.toBoundedContinuousFunction = 1 := by
    apply BoundedContinuousFunction.ext
    intro z
    rfl
  have hmass : πM Set.univ = 1 := by
    have e1 : (∫ _, (1:ℝ) ∂πM) = (πM Set.univ).toReal := by
      rw [integral_const, smul_eq_mul, mul_one, measureReal_def]
    have e2 : (∫ _, (1:ℝ) ∂πM) = ΛR one_cc := by
      have hriesz := RealRMK.integral_rieszMeasure ΛR one_cc
      have e : (fun x : X × Y => one_cc x) = (fun _ => (1:ℝ)) :=
        funext fun z => rfl
      rwa [← e]
    have h1 : (πM Set.univ).toReal = 1 := by
      rwa [← e1, e2, hΛR, eBCFone]
    have hne : πM Set.univ ≠ ∞ := measure_ne_top πM _
    have h := ENNReal.ofReal_toReal hne
    rwa [h1, ENNReal.ofReal_one] at h
  refine ⟨⟨πM, ⟨hmass⟩⟩, ?_, ?_⟩
  · constructor
    · change (μ : Measure X) = πM.map Prod.fst
      have hinter : ∀ f : C_c(X, ℝ), (∫ x, f x ∂(μ : Measure X))
        = ∫ x, f x ∂(πM.map Prod.fst) := by
        intro f
        have hfcont : Continuous (⇑f) := f.toBoundedContinuousFunction.continuous
        have hfmeas : AEStronglyMeasurable (⇑f) (πM.map Prod.fst) :=
          hfcont.aestronglyMeasurable
        have hmap : (∫ x, f x ∂(πM.map Prod.fst)) = ∫ z, f z.1 ∂πM :=
          integral_map measurable_fst.aemeasurable hfmeas
        have hriesz : (∫ z, f z.1 ∂πM) = ΛR (fstCC (Y := Y) f) :=
          RealRMK.integral_rieszMeasure ΛR (fstCC (Y := Y) f)
        have eBCF : (fstCC (Y := Y) f).toBoundedContinuousFunction
          = PhiLM (f.toBoundedContinuousFunction, 0) := by
          apply BoundedContinuousFunction.ext
          intro z
          change f z.1 = (PhiLM (f.toBoundedContinuousFunction, 0)) z
          rw [PhiLM_apply]
          change f z.1 = f z.1 + 0
          ring
        have hΛ : ΛR (fstCC (Y := Y) f)
          = Pim (PhiLM (f.toBoundedContinuousFunction, 0)) := by
          rw [hΛR, eBCF]
        have hPhi' := hPhi (f.toBoundedContinuousFunction, 0)
        have hL : (dualValLM (μ : Measure X) (ν : Measure Y)
          (f.toBoundedContinuousFunction, 0)) = ∫ x, f x ∂(μ : Measure X) := by
          have e : (dualValLM (μ : Measure X) (ν : Measure Y)
            (f.toBoundedContinuousFunction, 0))
            = (∫ x, f.toBoundedContinuousFunction x ∂(μ : Measure X))
              + ∫ y, (0 : Y →ᵇ ℝ) y ∂(ν : Measure Y) := rfl
          have z0 : (∫ y, (0 : Y →ᵇ ℝ) y ∂(ν : Measure Y)) = 0 := by
            have e0 : (fun y => (0 : Y →ᵇ ℝ) y) = (fun _ => (0:ℝ)) := rfl
            rw [e0]
            simp
          have ef : (fun x => f.toBoundedContinuousFunction x) = (fun x => f x) := rfl
          rw [e, z0, add_zero, ef]
        rwa [hmap, hriesz, hΛ, hPhi']
      exact MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported hinter
    · change (ν : Measure Y) = πM.map Prod.snd
      have hinter : ∀ g : C_c(Y, ℝ), (∫ y, g y ∂(ν : Measure Y))
        = ∫ y, g y ∂(πM.map Prod.snd) := by
        intro g
        have hgcont : Continuous (⇑g) := g.toBoundedContinuousFunction.continuous
        have hgmeas : AEStronglyMeasurable (⇑g) (πM.map Prod.snd) :=
          hgcont.aestronglyMeasurable
        have hmap : (∫ y, g y ∂(πM.map Prod.snd)) = ∫ z, g z.2 ∂πM :=
          integral_map measurable_snd.aemeasurable hgmeas
        have hriesz : (∫ z, g z.2 ∂πM) = ΛR (sndCC (X := X) g) :=
          RealRMK.integral_rieszMeasure ΛR (sndCC (X := X) g)
        have eBCF : (sndCC (X := X) g).toBoundedContinuousFunction
          = PhiLM (0, g.toBoundedContinuousFunction) := by
          apply BoundedContinuousFunction.ext
          intro z
          change g z.2 = (PhiLM (0, g.toBoundedContinuousFunction)) z
          rw [PhiLM_apply]
          change g z.2 = 0 + g z.2
          ring
        have hΛ : ΛR (sndCC (X := X) g)
          = Pim (PhiLM (0, g.toBoundedContinuousFunction)) := by
          rw [hΛR, eBCF]
        have hPhi' := hPhi (0, g.toBoundedContinuousFunction)
        have hL : (dualValLM (μ : Measure X) (ν : Measure Y)
          (0, g.toBoundedContinuousFunction)) = ∫ y, g y ∂(ν : Measure Y) := by
          have e : (dualValLM (μ : Measure X) (ν : Measure Y)
            (0, g.toBoundedContinuousFunction))
            = (∫ x, (0 : X →ᵇ ℝ) x ∂(μ : Measure X))
              + ∫ y, g.toBoundedContinuousFunction y ∂(ν : Measure Y) := rfl
          have z0 : (∫ x, (0 : X →ᵇ ℝ) x ∂(μ : Measure X)) = 0 := by
            have e0 : (fun x => (0 : X →ᵇ ℝ) x) = (fun _ => (0:ℝ)) := rfl
            rw [e0]
            simp
          have ef : (fun y => g.toBoundedContinuousFunction y) = (fun y => g y) := rfl
          rw [e, z0, zero_add, ef]
        rwa [hmap, hriesz, hΛ, hPhi']
      exact MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported hinter
  · change (∫ z, c z ∂πM) ≤ Dstar + ε
    set costCC : C_c(X × Y, ℝ) :=
      CompactlySupportedContinuousMap.continuousMapEquiv ⟨c, hc⟩ with hcostCC
    have hriesz : (∫ z, c z ∂πM) = ΛR costCC :=
      RealRMK.integral_rieszMeasure ΛR costCC
    have eBCF : costCC.toBoundedContinuousFunction = mkBCF c hc := by
      apply BoundedContinuousFunction.ext
      intro z
      rfl
    rwa [hriesz, hΛR, eBCF]

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
[kantorovich_duality_compact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean)
-/
@[path]
private lemma kantorovich_duality_compact_eq
  [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y}
  {c : X × Y → ℝ}
-- given
  (hc : Continuous c) :
-- imply
  sInf (primalValues μ ν c) =
    sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
    DualFeasible c φ ψ ∧
    r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
-- proof
  apply MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted.kantorovich_duality_compact μ ν c hc


-- created on 2026-10-20
-- updated on 2026-10-23
