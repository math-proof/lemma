/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Order.Compact
import Def.MeasureTheory.OptimalTransport.Kantorovich.Part5


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-- Separation produces a positive linear functional dominating the dual objective. -/
theorem exists_posFunctional
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Pim : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ,
      (∀ w, (∀ z, 0 ≤ w z) → 0 ≤ Pim w) ∧
      (∀ d, Pim (PhiLM d) = dualValLM (μ : Measure X) (ν : Measure Y) d) ∧
      Pim (mkBCF c hc) ≤ sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
        DualFeasible c φ ψ ∧
        r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} + ε ∧
      Pim 1 = 1 := by
  set Dstar : ℝ := sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}
  have hD : ∀ (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ),
      (∀ z, (PhiLM d) z - c z ≤ m) →
      (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ Dstar :=
    fun d m hm => key_le μ ν c hc d m hm
  have hdisj := disjoint_graph_sepSet μ ν c hc Dstar ε hε hD
  have hUopen : IsOpen (sepSet (mkBCF c hc) (Dstar + ε)) := isOpen_sepSet _ _
  have hUconv : Convex ℝ (sepSet (mkBCF c hc) (Dstar + ε)) := convex_sepSet _ _
  have hMconv := Submodule.convex (graphSub (μ : Measure X) (ν : Measure Y))
  obtain ⟨F, γ, hUs, hMt⟩ := geometric_hahn_banach_open hUconv hUopen hMconv hdisj
  have hF0 : ∀ m : ((X × Y) →ᵇ ℝ) × ℝ,
      m ∈ (graphSub (μ : Measure X) (ν : Measure Y)) → F m = 0 := by
    intro m hm
    by_contra hne
    have hmem : ((γ - 1) / F m) • m ∈ (graphSub (μ : Measure X) (ν : Measure Y)) :=
      Submodule.smul_mem _ _ hm
    have hle := hMt _ hmem
    have hFm : F (((γ - 1) / F m) • m) = γ - 1 := by
      rw [F.map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
    linarith
  set Λ : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ := F.toLinearMap.comp (LinearMap.inl ℝ _ _)
  have hΛeq : ∀ v, Λ v = F (v, 0) := fun v => rfl
  have hdecomp : ∀ p : ((X × Y) →ᵇ ℝ) × ℝ, F p = Λ p.1 + p.2 * F (0, 1) := by
    intro p
    have e : p = (p.1, 0) + p.2 • (0, 1) := by
      rw [Prod.ext_iff]
      constructor
      · change p.1 = p.1 + p.2 • (0 : (X × Y) →ᵇ ℝ)
        rw [smul_zero, add_zero]
      · change p.2 = (0 : ℝ) + p.2 • (1 : ℝ)
        rw [smul_eq_mul, mul_one, zero_add]
    conv_lhs => rw [e]
    rw [map_add, F.map_smul, smul_eq_mul, hΛeq]
  have h0mem : (0 : ((X × Y) →ᵇ ℝ) × ℝ)
      ∈ (graphSub (μ : Measure X) (ν : Measure Y)) := ⟨0, map_zero _⟩
  have hγ0 : γ ≤ 0 := by
    have hle := hMt _ h0mem
    rw [map_zero] at hle
    exact hle
  have hFne : F ≠ 0 := by
    intro hF0'
    obtain ⟨p₀, hp₀⟩ := nonempty_sepSet (mkBCF c hc) (Dstar + ε)
    have h1 := hUs p₀ hp₀
    have h2 := hMt _ h0mem
    rw [hF0'] at h1 h2
    simp at h1 h2
    linarith
  have hmemCB : ∀ t : ℝ, Dstar + ε < t →
      (mkBCF c hc, t) ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
    intro t ht
    rw [sepSet_mem]
    intro z
    linarith
  have hα0 : F (0, 1) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set T : ℝ := max (Dstar + ε + 1) ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) with hT
    have hT1 : Dstar + ε < T := by
      rw [hT]
      exact lt_max_iff.mpr (Or.inl (by linarith))
    have hlt := hUs _ (hmemCB T hT1)
    rw [hdecomp] at hlt
    have hlt' : Λ (mkBCF c hc) + T * F (0, 1) < γ := hlt
    have hT2 : ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) ≤ T := by
      rw [hT]
      exact le_max_right _ _
    have hmul : ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) * F (0, 1)
        = γ - F (mkBCF c hc, 0) + 1 := div_mul_cancel₀ _ (ne_of_gt hpos)
    have hge : γ - F (mkBCF c hc, 0) + 1 ≤ T * F (0, 1) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hT2 (le_of_lt hpos)
    have hΛcb : Λ (mkBCF c hc) = F (mkBCF c hc, 0) := hΛeq _
    linarith
  have hpos : ∀ w : (X × Y) →ᵇ ℝ, (∀ z, 0 ≤ w z) → 0 ≤ F (w, 0) := by
    intro w hw
    by_contra hneg
    push Not at hneg
    have hmem : ∀ s : ℝ, 0 ≤ s →
        (mkBCF c hc - s • w, Dstar + ε + 1)
          ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
      intro s hs
      rw [sepSet_mem]
      intro z
      have e1 : (mkBCF c hc - s • w) z = (mkBCF c hc) z - s * w z := by
        rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
          smul_eq_mul]
      rw [e1]
      have hsw : 0 ≤ s * w z := mul_nonneg hs (hw z)
      have hD' : (Dstar + ε + 1) - (Dstar + ε) = 1 := by ring
      rw [hD']
      linarith
    set K : ℝ := |F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ| + 1 with hK
    have hKpos : 0 < K := by
      rw [hK]
      linarith [abs_nonneg (F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ)]
    set s : ℝ := K / (-F (w, 0)) with hs
    have hne : -F (w, 0) ≠ 0 := neg_ne_zero.mpr (ne_of_lt hneg)
    have hs0 : 0 ≤ s := by
      rw [hs]
      exact div_nonneg (le_of_lt hKpos) (le_of_lt (neg_pos.mpr hneg))
    have hlt := hUs _ (hmem s hs0)
    rw [hdecomp] at hlt
    have hlt' : Λ (mkBCF c hc - s • w) + (Dstar + ε + 1) * F (0, 1) < γ := hlt
    have hdec : Λ (mkBCF c hc - s • w)
        = Λ (mkBCF c hc) - s * Λ w := by
      simp only [map_sub, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
    rw [hdec] at hlt'
    have hsk : s * (-F (w, 0)) = K := by rw [hs]; exact div_mul_cancel₀ _ hne
    have hsk2 : -(s * F (w, 0)) = K := by rw [← hsk]; ring
    have hΛw : Λ w = F (w, 0) := hΛeq _
    have hsk3 : Λ (mkBCF c hc) - s * Λ w = Λ (mkBCF c hc) + K := by
      rw [hΛw, ← hsk2]; ring
    rw [hsk3, hK] at hlt'
    have habs := neg_le_abs (F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ)
    have hΛcb : Λ (mkBCF c hc) = F (mkBCF c hc, 0) := hΛeq _
    linarith
  have hgraph : ∀ d : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
      Λ (PhiLM d) + (dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1) = 0 := by
    intro d
    have hm : (PhiLM d, dualValLM (μ : Measure X) (ν : Measure Y) d)
        ∈ (graphSub (μ : Measure X) (ν : Measure Y)) := ⟨d, rfl⟩
    have h0 := hF0 _ hm
    rw [hdecomp] at h0
    have h0' : Λ (PhiLM d)
        + (dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1) = 0 := h0
    exact h0'
  have hαne : F (0, 1) ≠ 0 := by
    intro hα0
    have hΛlt : ∀ v : (X × Y) →ᵇ ℝ, F (v, 0) < γ := by
      intro v
      obtain ⟨z₀, hz₀⟩ := exists_max_attain (v - mkBCF c hc)
      have hmem : (v, Dstar + ε + (v - mkBCF c hc) z₀ + 1)
          ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
        rw [sepSet_mem]
        intro z
        have hle : v z - (mkBCF c hc) z ≤ (v - mkBCF c hc) z₀ := by
          have h := hz₀ z
          have e : ∀ w : X × Y, (v - mkBCF c hc) w = v w - (mkBCF c hc) w :=
            fun w => rfl
          rwa [e z] at h
        linarith
      have h := hUs _ hmem
      rw [hdecomp] at h
      have h' : Λ v + (Dstar + ε + (v - mkBCF c hc) z₀ + 1) * F (0, 1) < γ := h
      rw [hα0, mul_zero, add_zero] at h'
      rw [hΛeq] at h'
      exact h'
    have hΛ0 : ∀ v : (X × Y) →ᵇ ℝ, F (v, 0) = 0 := by
      intro v
      by_contra hnev
      have hlt := hΛlt (((γ + 1) / F (v, 0)) • v)
      have hsc : F ((((γ + 1) / F (v, 0)) • v), 0) = γ + 1 := by
        have e1 : F ((((γ + 1) / F (v, 0)) • v), 0)
            = Λ ((((γ + 1) / F (v, 0)) • v)) := (hΛeq _).symm
        rw [e1, map_smulₛₗ, RingHom.id_apply, smul_eq_mul, hΛeq]
        exact div_mul_cancel₀ _ hnev
      linarith
    have hFall : F = 0 := by
      apply ContinuousLinearMap.ext
      intro p
      rw [hdecomp]
      have h1 : Λ p.1 = 0 := by rw [hΛeq]; exact hΛ0 p.1
      rw [h1, hα0, mul_zero, add_zero]
      rfl
    exact hFne hFall
  have hαneg : F (0, 1) < 0 := lt_of_le_of_ne hα0 hαne
  have hsmul : ∀ v : (X × Y) →ᵇ ℝ,
      (((-F (0, 1))⁻¹ • Λ) v) = (-F (0, 1))⁻¹ * Λ v := by
    intro v
    rw [LinearMap.smul_apply, smul_eq_mul]
  have hPimPhi : ∀ d : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
      (((-F (0, 1))⁻¹ • Λ) (PhiLM d))
        = dualValLM (μ : Measure X) (ν : Measure Y) d := by
    intro d
    rw [hsmul]
    have hgr := hgraph d
    have hF0' : Λ (PhiLM d)
        = -((dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1)) := by
      linarith
    rw [hF0']
    have hαne' : -F (0, 1) ≠ 0 := neg_ne_zero.mpr hαne
    have hinv : (-F (0, 1))⁻¹ * (-F (0, 1)) = 1 := inv_mul_cancel₀ hαne'
    linear_combination (dualValLM (μ : Measure X) (ν : Measure Y) d) * hinv
  have hposPim : ∀ w : (X × Y) →ᵇ ℝ, (∀ z, 0 ≤ w z)
      → 0 ≤ (((-F (0, 1))⁻¹ • Λ) w) := by
    intro w hw
    rw [hsmul]
    have hΛw : 0 ≤ Λ w := by rw [hΛeq]; exact hpos w hw
    have hpos2 : (0:ℝ) ≤ (-F (0, 1))⁻¹ :=
      le_of_lt (inv_pos.mpr (neg_pos.mpr hαneg))
    exact mul_nonneg hpos2 hΛw
  have hlePim : (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc)) ≤ Dstar + ε := by
    have hpos2 : (0:ℝ) < (-F (0, 1))⁻¹ := inv_pos.mpr (neg_pos.mpr hαneg)
    have hlt : ∀ t : ℝ, Dstar + ε < t
        → Λ (mkBCF c hc) + t * F (0, 1) < γ := by
      intro t ht
      have h := hUs _ (hmemCB t ht)
      rw [hdecomp] at h
      have h' : Λ (mkBCF c hc) + t * F (0, 1) < γ := h
      exact h'
    have hPimlt : ∀ t : ℝ, Dstar + ε < t →
        (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc)) < t + (-F (0, 1))⁻¹ * γ := by
      intro t ht
      rw [hsmul]
      have h := hlt t ht
      have hmul := mul_lt_mul_of_pos_left h hpos2
      have hαne' : -F (0, 1) ≠ 0 := neg_ne_zero.mpr hαne
      have hinv : (-F (0, 1))⁻¹ * (-F (0, 1)) = 1 := inv_mul_cancel₀ hαne'
      have h2 : (-F (0, 1))⁻¹ * (t * F (0, 1)) = -t := by
        linear_combination (-t) * hinv
      have heq : (-F (0, 1))⁻¹ * (Λ (mkBCF c hc) + t * F (0, 1))
          = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) - t := by
        calc (-F (0, 1))⁻¹ * (Λ (mkBCF c hc) + t * F (0, 1))
            = (-F (0, 1))⁻¹ * Λ (mkBCF c hc)
              + (-F (0, 1))⁻¹ * (t * F (0, 1)) := by ring
          _ = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) + (-t) := by rw [h2]
          _ = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) - t := by ring
      linarith
    have hle1 : (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc))
        ≤ Dstar + ε + (-F (0, 1))⁻¹ * γ := by
      apply le_of_forall_gt_imp_ge_of_dense
      intro b hb
      have ht : Dstar + ε
          < Dstar + ε + (b - (Dstar + ε + (-F (0, 1))⁻¹ * γ)) / 2 := by
        have hδ : (0:ℝ) < b - (Dstar + ε + (-F (0, 1))⁻¹ * γ) := by linarith
        linarith
      have h := hPimlt _ ht
      linarith
    have hcorr : (-F (0, 1))⁻¹ * γ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos2) hγ0
    linarith
  have h1Pim : (((-F (0, 1))⁻¹ • Λ) 1) = 1 := by
    have h1 : (1 : (X × Y) →ᵇ ℝ) = PhiLM (1, 0) := by
      apply BoundedContinuousFunction.ext
      intro z
      rw [PhiLM_apply]
      have e1 : ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 z.1 = 1 := rfl
      have e2 : ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 z.2 = 0 := rfl
      have e3 : (1 : (X × Y) →ᵇ ℝ) z = 1 := rfl
      rw [e1, e2, e3]
      ring
    rw [h1]
    rw [hPimPhi]
    have hL1 : (dualValLM (μ : Measure X) (ν : Measure Y) (1, 0)) = 1 := by
      have e : (dualValLM (μ : Measure X) (ν : Measure Y) (1, 0))
          = (∫ x, ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 x ∂(μ : Measure X))
            + ∫ y, ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 y ∂(ν : Measure Y) := rfl
      rw [e]
      have e1 : (fun x => ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 x)
          = (fun _ => (1:ℝ)) := rfl
      have e2 : (fun y => ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 y)
          = (fun _ => (0:ℝ)) := rfl
      rw [e1, e2]
      have i1 : (∫ _, (1:ℝ) ∂(μ : Measure X)) = 1 := by simp
      have i0 : (∫ _, (0:ℝ) ∂(ν : Measure Y)) = 0 := by simp
      rw [i1, i0, add_zero]
    exact hL1
  exact ⟨(-F (0, 1))⁻¹ • Λ, hposPim, hPimPhi, hlePim, h1Pim⟩

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
