import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionDensity
open MeasureTheory Filter Topology Function Set TestFunctions SchwartzMap ConvolutionDensity
open scoped ZeroAtInfty Convolution
open scoped ContDiff
open Filter Topology SchwartzMap
open SchwartzMap
open scoped SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace


namespace ConvolutionDensity

/--
[approxIdentity_tendstoUniformly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma approxIdentity_tendstoUniformly
  [SeminormedAddCommGroup G]
  [MeasurableSpace G]
  [BorelSpace G]
  [SecondCountableTopology G]
  {μ : Measure G}
  [μ.IsAddLeftInvariant]
  [SFinite μ]
  {l : Filter ι}
  {φ : ι → G → ℝ}
  {f : C₀(G, ℝ)}
-- given
  (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
  (hiφ : ∀ᶠ i in l, ∫ x, φ i x ∂μ = 1)
  (hφ : Tendsto (fun i => support (φ i)) l (𝓝 (0 : G)).smallSets)
  (hmφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) μ) :
-- imply
  TendstoUniformly (fun i => (φ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f : G → ℝ))) (f : G → ℝ) l := by
-- proof
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have huc := ZeroAtInftyContinuousMap.uniformContinuous f
  rw [Metric.uniformContinuous_iff] at huc
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hfδ⟩ := huc (ε / 2) hε2
  rw [tendsto_smallSets_iff] at hφ
  have hφδ := hφ (Metric.ball 0 δ) (Metric.ball_mem_nhds 0 hδ)
  filter_upwards [hnφ, hiφ, hφδ, hmφ] with i hnφi hiφi hφi hmφi
  intro x
  rw [dist_comm]
  calc dist ((φ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
    (f : G → ℝ)) x) (f x)
    ≤ ε / 2 := dist_convolution_le hε2.le hφi hnφi hiφi
      (map_continuous f).aestronglyMeasurable
      (fun y hy => le_of_lt (hfδ (Metric.mem_ball.mp hy)))
    _ < ε := half_lt_self hε

end ConvolutionDensity

namespace ConvolutionDensity

/--
[ckNorm_convolution_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma ckNorm_convolution_threshold
  {n : ℕ}
  {k : ℕ}
  {v : EuclideanSpace ℝ (Fin n) → ℂ}
  {ε : ℝ}
-- given
  (hv_supp : HasCompactSupport v)
  (hv_smooth : ContDiff ℝ k v)
  (hε : 0 < ε) :
-- imply
  ∃ r : ℝ, 0 < r ∧ ∀ ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)), ψ.rOut ≤ r → ckNorm n k (fun x => v x - (ψ.normed (volume : Measure (EuclideanSpace ℝ (Fin n))) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x) < ε := by
-- proof
  induction k generalizing v ε with
  | zero =>
    have hv_cont := hv_smooth.continuous
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
      (hv_supp.uniformContinuous_of_continuous hv_cont) (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun ψ hψ => ?_⟩
    show ⨆ x, ‖v x - _‖ < ε
    calc ⨆ x, ‖v x - (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x‖
      ≤ ε / 2 := ciSup_le fun x₀ => by
        rw [← dist_eq_norm, dist_comm]
        exact ψ.dist_normed_convolution_le hv_cont.aestronglyMeasurable fun y hy =>
          (hfδ (lt_of_lt_of_le (Metric.mem_ball.mp hy) hψ)).le
      _ < ε := by linarith
  | succ k ih =>
    have hv_cont := hv_smooth.continuous
    have hv_k : ContDiff ℝ k v := hv_smooth.of_le (by exact_mod_cast Nat.le_succ k)
    set m := (1 : ℝ) + ↑n
    have hm : 0 < m := by positivity
    have hε' : 0 < ε / m := div_pos hε hm
    obtain ⟨r₀, hr₀, h₀⟩ := ih v hv_supp hv_k (ε / m) hε'
    have hDj : ∀ j : Fin n,
      ∃ rj : ℝ, 0 < rj ∧ ∀ ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)),
        ψ.rOut ≤ rj →
        ckNorm n k (fun x => fderiv ℝ v x (EuclideanSpace.single j 1) -
          (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (fun y => fderiv ℝ v y (EuclideanSpace.single j 1))) x) < ε / m := by
      intro j
      have hDj_supp : HasCompactSupport (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) := by
        change HasCompactSupport ((fun L : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ) =>
          L (EuclideanSpace.single j 1)) ∘ fderiv ℝ v)
        exact (hv_supp.fderiv ℝ).comp_left (by simp)
      have hDj_smooth : ContDiff ℝ k (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) :=
        (hv_smooth.fderiv_right (m := k)
          (by exact_mod_cast Nat.lt_succ_of_le le_rfl)).clm_apply contDiff_const
      exact ih _ hDj_supp hDj_smooth (ε / m) hε'
    choose rj hrj_pos hrj using hDj
    by_cases hn : n = 0
    ·
      subst hn
      refine ⟨r₀, hr₀, fun ψ hψ => ?_⟩
      simp only [ckNorm, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have := h₀ ψ hψ
      simp only [m, Nat.cast_zero, add_zero, div_one] at this
      exact this
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
      set r := min r₀ (Finset.univ.inf' Finset.univ_nonempty rj)
      have hr_pos : 0 < r := lt_min hr₀ (by
        simp only [Finset.lt_inf'_iff]; exact fun j _ => hrj_pos j)
      have hψ_rj : ∀ (ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))), ψ.rOut ≤ r →
        ∀ j : Fin n, ψ.rOut ≤ rj j := fun ψ hψ j =>
        le_trans hψ (le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ j)))
      refine ⟨r, hr_pos, fun ψ hψ => ?_⟩
      show ckNorm n (k + 1) _ < ε
      simp only [ckNorm]
      have hψ_r₀ : ψ.rOut ≤ r₀ := le_trans hψ (min_le_left _ _)
      have h_main := h₀ ψ hψ_r₀
      have h_deriv : ∀ j : Fin n,
        ckNorm n k (fun x => fderiv ℝ (fun y => v y -
          (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) x
          (EuclideanSpace.single j 1)) < ε / m := by
        intro j
        have hv_diff : Differentiable ℝ v := hv_smooth.differentiable (by
          show (↑(k + 1) : WithTop ℕ∞) ≠ 0; exact_mod_cast Nat.succ_ne_zero k)
        have hg_diff : Differentiable ℝ (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) :=
          (ψ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤)
            _ ψ.contDiff_normed hv_cont.locallyIntegrable).differentiable
              (by exact_mod_cast ENat.top_ne_zero)
        have heq : (fun x => fderiv ℝ (fun y => v y -
          (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) x
          (EuclideanSpace.single j 1)) =
          (fun x => fderiv ℝ v x (EuclideanSpace.single j 1) -
            (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              (fun y => fderiv ℝ v y (EuclideanSpace.single j 1))) x) := by
          ext x
          rw [show (fun y => v y - (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) =
            v - (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) from rfl,
            fderiv_sub (hv_diff x) (hg_diff x), ContinuousLinearMap.sub_apply]
          congr 1
          have hf_loc : LocallyIntegrable (ψ.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) volume :=
            ψ.integrable_normed.locallyIntegrable
          have hv1 : ContDiff ℝ 1 v := hv_smooth.of_le (by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
          rw [(hv_supp.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
            hf_loc hv1 x).fderiv]
          exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf_loc (hv_supp.fderiv ℝ)
            (hv1.continuous_fderiv one_ne_zero) x (EuclideanSpace.single j 1)
        rw [heq]
        exact hrj j ψ (hψ_rj ψ hψ j)
      have h_sum : Finset.sum Finset.univ (fun j : Fin n =>
        ckNorm n k (fun x => fderiv ℝ (fun y => v y -
          (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) x
          (EuclideanSpace.single j 1))) < ↑n * (ε / m) := by
        calc _ < Finset.sum Finset.univ (fun _ : Fin n => ε / m) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h_deriv j)
          _ = ↑(Fintype.card (Fin n)) * (ε / m) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ↑n * (ε / m) := by simp [Fintype.card_fin]
      calc ckNorm n k (fun x => v x - _) +
        Finset.sum Finset.univ (fun j => ckNorm n k (fun x =>
          fderiv ℝ (fun y => v y - _) x (EuclideanSpace.single j 1)))
        < ε / m + ↑n * (ε / m) := by linarith
        _ = ε := by show ε / m + ↑n * (ε / m) = ε; field_simp [show m ≠ 0 from ne_of_gt hm]; ring

end ConvolutionDensity

namespace ConvolutionDensity

/--
[approx_compactly_supported_Ck_by_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma approx_compactly_supported_Ck_by_schwartz
  {n : ℕ}
  {k : ℕ}
  {v : EuclideanSpace ℝ (Fin n) → ℂ}
  {ε : ℝ}
-- given
  (hv_supp : HasCompactSupport v)
  (hv_smooth : ContDiff ℝ k v)
  (hε : 0 < ε) :
-- imply
  ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ckNorm n k (fun x => v x - φ x) < ε := by
-- proof
  obtain ⟨r, hr, hbound⟩ := ckNorm_convolution_threshold k v hv_supp hv_smooth ε hε
  let ψ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨r / 2, r, by linarith, by linarith⟩
  set μ : Measure (EuclideanSpace ℝ (Fin n)) := volume
  set g := ψ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] v
  have hg_supp : HasCompactSupport g := ψ.hasCompactSupport_normed.convolution _ hv_supp
  have hg_smooth : ContDiff ℝ (↑⊤ : ℕ∞) g :=
    ψ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤) _
      ψ.contDiff_normed hv_smooth.continuous.locallyIntegrable
  refine ⟨hg_supp.toSchwartzMap hg_smooth, ?_⟩
  have hφ_eq : ∀ x, (hg_supp.toSchwartzMap hg_smooth : EuclideanSpace ℝ (Fin n) → ℂ) x = g x :=
    hg_supp.toSchwartzMap_toFun hg_smooth
  have : (fun x => v x - (hg_supp.toSchwartzMap hg_smooth) x) = (fun x => v x - g x) := by
    ext x; simp [hφ_eq]
  rw [this]
  exact hbound ψ le_rfl

end ConvolutionDensity

namespace ConvolutionDensity

/--
[ckNorm_add_le_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma ckNorm_add_le_base
  {n : ℕ}
  {f g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hf : BddAbove (Set.range fun x => ‖f x‖))
  (hg : BddAbove (Set.range fun x => ‖g x‖)) :
-- imply
  ckNorm n 0 (fun x => f x + g x) ≤ ckNorm n 0 f + ckNorm n 0 g := by
-- proof
  show (⨆ x, ‖f x + g x‖) ≤ (⨆ x, ‖f x‖) + (⨆ x, ‖g x‖)
  apply ciSup_le
  intro x
  calc ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ (⨆ y, ‖f y‖) + (⨆ y, ‖g y‖) := by
      gcongr
      · exact le_ciSup hf x
      · exact le_ciSup hg x

end ConvolutionDensity

namespace ConvolutionDensity

/--
[ckNorm_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma ckNorm_add_le
  {n : ℕ}
  {k : ℕ}
  {f g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hf : CkNormBdd n k f)
  (hg : CkNormBdd n k g) :
-- imply
  ckNorm n k (fun x => f x + g x) ≤ ckNorm n k f + ckNorm n k g := by
-- proof
  induction k generalizing f g with
  | zero => exact ckNorm_add_le_base f g hf hg
  | succ k ih =>
    simp only [ckNorm]
    have hf_bdd := hf.1
    have hf_diff := hf.2.1
    have hg_bdd := hg.1
    have hg_diff := hg.2.1
    have h_main := ih f g hf_bdd hg_bdd
    have h_sum : ∀ j : Fin n, ∀ x,
      fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1) =
      fderiv ℝ f x (EuclideanSpace.single j 1) + fderiv ℝ g x (EuclideanSpace.single j 1) := by
      intro j x
      have : fderiv ℝ (fun x => f x + g x) x = fderiv ℝ f x + fderiv ℝ g x := by
        have : (fun x => f x + g x) = f + g := rfl
        rw [this, fderiv_add (hf_diff x) (hg_diff x)]
      rw [this, ContinuousLinearMap.add_apply]
    have h_deriv_sum : ∀ j : Fin n,
      ckNorm n k (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1)) ≤
      ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) +
      ckNorm n k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) := by
      intro j
      have heq : (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1)) =
        (fun x => fderiv ℝ f x (EuclideanSpace.single j 1) +
          fderiv ℝ g x (EuclideanSpace.single j 1)) := by
        ext x; exact h_sum j x
      rw [heq]
      exact ih _ _ (hf.2.2 j) (hg.2.2 j)
    have h_sum_le : Finset.sum Finset.univ (fun j =>
      ckNorm n k (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1))) ≤
      Finset.sum Finset.univ (fun j =>
        ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1))) +
      Finset.sum Finset.univ (fun j =>
        ckNorm n k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1))) := by
      calc Finset.sum Finset.univ (fun j =>
        ckNorm n k (fun x => fderiv ℝ (fun x => f x + g x) x (EuclideanSpace.single j 1)))
        _ ≤ Finset.sum Finset.univ (fun j =>
          (ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) +
            ckNorm n k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)))) := by
          gcongr with j _
          exact h_deriv_sum j
        _ = _ := Finset.sum_add_distrib
    linarith
/-- Schwartz functions are dense in the space of `C^k` zero-at-infinity
functions: any such `u` can be approximated in the `C^k` norm to within `ε`
by a Schwartz function. The proof first approximates `u` by a compactly
supported `C^k` function, then approximates that by a Schwartz function via
mollification. -/
section CompactSupportSchwartz
open scoped ContDiff

end ConvolutionDensity

namespace ConvolutionDensity

/--
[hasCompactSupport_mul_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma hasCompactSupport_mul_of_left
  {n : ℕ}
  {μ : EuclideanSpace ℝ (Fin n) → ℂ}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hμ_cpt : HasCompactSupport μ) :
-- imply
  HasCompactSupport (fun x => μ x * g x) :=
-- proof
  hμ_cpt.mul_right

end ConvolutionDensity

namespace ConvolutionDensity

/--
[contDiff_mul_of_both](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma contDiff_mul_of_both
  {n : ℕ}
  {μ : EuclideanSpace ℝ (Fin n) → ℂ}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hμ_smooth : ContDiff ℝ ∞ μ)
  (hg_smooth : ContDiff ℝ ∞ g) :
-- imply
  ContDiff ℝ ∞ (fun x => μ x * g x) :=
-- proof
  hμ_smooth.mul hg_smooth
end ConvolutionDensity
section CompactSupportDenseSchwartz
open Filter Topology SchwartzMap


/--
[compactSupport_dense_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma compactSupport_dense_schwartz
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [HasContDiffBump E] :
-- imply
  Dense {f : SchwartzMap E F | HasCompactSupport f} := by
-- proof
  rw [dense_iff_closure_eq]
  ext f
  simp only [Set.mem_univ, iff_true]
  have htendsto : Tendsto (fun m => bumpCutoffMul m f) atTop (nhds f) := by
    rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds _ f]
    intro ⟨k, j⟩ ε hε
    have h1 : Tendsto (fun m => (SchwartzMap.seminorm ℝ k j) (f - bumpCutoffMul m f))
      atTop (nhds 0) :=
      seminorm_cutoff_sub_tendsto ℝ f k j
    have h2 : ∀ᶠ m in atTop, (SchwartzMap.seminorm ℝ k j) (f - bumpCutoffMul m f) < ε :=
      h1 (Iio_mem_nhds hε)
    exact h2.mono fun m hm => by
      rw [show bumpCutoffMul m f - f = -(f - bumpCutoffMul m f) from
        (neg_sub f (bumpCutoffMul m f)).symm, map_neg_eq_map]
      exact hm
  exact mem_closure_of_tendsto htendsto
    (Eventually.of_forall fun m => bumpCutoffMul_hasCompactSupport m f)
end CompactSupportDenseSchwartz
section CutoffSchwartz
open SchwartzMap
set_option maxHeartbeats 3200000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
[SchwartzMap.cutoffMul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean)
-/
@[path]
lemma SchwartzMap.cutoffMul_apply
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {φ : E → ℝ}
  {f : SchwartzMap E F}
  {x : E}
-- given
  (hφcs : HasCompactSupport φ)
  (hφcd : ContDiff ℝ ⊤ φ) :
-- imply
  (SchwartzMap.cutoffMul φ hφcs hφcd f) x = φ x • f x := by
-- proof
  simp [SchwartzMap.cutoffMul, HasCompactSupport.toSchwartzMap_toFun]
end CutoffSchwartz
open scoped SchwartzMap
namespace ConvolutionDensity
end ConvolutionDensity
open SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace
noncomputable section
namespace ConvolutionDensity
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


-- created on 2026-10-23
