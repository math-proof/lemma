/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.Compact.Basic

noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory
open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure on the compact group `G`. -/
private def pwHaar (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    Measure G :=
  Measure.haar (G := G)

/-- Haar measure on a compact group satisfies the Haar typeclass. -/
private instance pwHaarIsHaar (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    MeasureTheory.Measure.IsHaarMeasure (pwHaar G) :=
  MeasureTheory.Measure.isHaarMeasure_haarMeasure _

/-- Left translation on `L²(G, μ; ℂ)`: `(pwTransl g f) x = f (g⁻¹ * x)` a.e. -/
private noncomputable def pwTransl (g : G) :
    Lp ℂ 2 (pwHaar G) →ₗᵢ[ℂ] Lp ℂ 2 (pwHaar G) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => g⁻¹ * x)
    (measurePreserving_mul_left (pwHaar G) g⁻¹)

/-- Kernel section at `g`: the continuous map `h ↦ conj (k (h⁻¹ * g))`. -/
private noncomputable def pwPhiKer (k : C(G, ℂ)) (g : G) : C(G, ℂ) :=
  ⟨fun h => conj (k (h⁻¹ * g)),
    Complex.continuous_conj.comp
      (k.continuous.comp (continuous_id.inv.mul_const g))⟩

/-- `Φ g` is the kernel section viewed in `L²`. -/
private noncomputable def pwPhi (k : C(G, ℂ)) (g : G) : Lp ℂ 2 (pwHaar G) :=
  ContinuousMap.toLp 2 (pwHaar G) ℂ (pwPhiKer (G := G) k g)

/-- `Φ` is continuous in `g`. -/
private theorem pwPhi_continuous (k : C(G, ℂ)) :
    Continuous (pwPhi (G := G) k) := by
  have hK : Continuous (fun p : G × G => conj (k (p.2⁻¹ * p.1))) :=
    Complex.continuous_conj.comp
      (k.continuous.comp (continuous_snd.inv.mul continuous_fst))
  have hfun : pwPhi (G := G) k
      = ⇑(ContinuousMap.toLp 2 (pwHaar G) ℂ) ∘
        ⇑(⟨fun p : G × G => conj (k (p.2⁻¹ * p.1)), hK⟩ : C(G × G, ℂ)).curry := by
    funext g
    simp only [Function.comp_apply]
    change ContinuousMap.toLp 2 (pwHaar G) ℂ _ = _
    congr 1
  rw [hfun]
  exact (ContinuousMap.toLp 2 (pwHaar G) ℂ).continuous.comp
    (⟨fun p : G × G => conj (k (p.2⁻¹ * p.1)), hK⟩ : C(G × G, ℂ)).curry.continuous

/-- Uniform bound on `‖Φ g‖`. -/
private theorem pwPhi_bound (k : C(G, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ‖pwPhi (G := G) k g‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (pwPhi_continuous (G := G) k).continuousOn
  exact ⟨‖C‖, norm_nonneg _, fun g => (hC g (Set.mem_univ g)).trans (le_abs_self C)⟩

/-- `T0 f` is the continuous function `g ↦ ⟪Φ g, f⟫`. -/
private noncomputable def pwT0Map (k : C(G, ℂ)) (f : Lp ℂ 2 (pwHaar G)) : C(G, ℂ) :=
  ⟨fun g => ⟪pwPhi (G := G) k g, f⟫,
    (pwPhi_continuous (G := G) k).inner continuous_const⟩

/-- Application of `T0 f`. -/
private theorem pwT0Map_apply (k : C(G, ℂ)) (f : Lp ℂ 2 (pwHaar G)) (g : G) :
    (pwT0Map (G := G) k f) g = ⟪pwPhi (G := G) k g, f⟫ :=
  rfl

/-- `T0` as a linear map into `C(G, ℂ)`. -/
private noncomputable def pwT0Lin (k : C(G, ℂ)) :
    (Lp ℂ 2 (pwHaar G)) →ₗ[ℂ] C(G, ℂ) :=
  { toFun := fun f => pwT0Map (G := G) k f
    map_add' := by
      intro f g
      ext t
      simp only [pwT0Map_apply, ContinuousMap.add_apply]
      exact inner_add_right _ _ _
    map_smul' := by
      intro c f
      ext t
      simp only [pwT0Map_apply, ContinuousMap.smul_apply]
      exact inner_smul_right _ _ _ }

/-- `T0` as a continuous linear map into `C(G, ℂ)`. -/
private noncomputable def pwT0 (k : C(G, ℂ)) :
    (Lp ℂ 2 (pwHaar G)) →L[ℂ] C(G, ℂ) :=
  (pwT0Lin (G := G) k).mkContinuousOfExistsBound (by
    obtain ⟨C, hC0, hC⟩ := pwPhi_bound (G := G) k
    refine ⟨C, fun f => ?_⟩
    change ‖pwT0Map (G := G) k f‖ ≤ C * ‖f‖
    rw [ContinuousMap.norm_le _ (mul_nonneg hC0 (norm_nonneg f))]
    intro g
    rw [pwT0Map_apply]
    calc ‖⟪pwPhi (G := G) k g, f⟫‖ ≤ ‖pwPhi (G := G) k g‖ * ‖f‖ :=
          norm_inner_le_norm _ _
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (hC g) (norm_nonneg f))

/-- `T` is `toLp` after `T0`. -/
private noncomputable def pwT (k : C(G, ℂ)) :
    (Lp ℂ 2 (pwHaar G)) →L[ℂ] Lp ℂ 2 (pwHaar G) :=
  (ContinuousMap.toLp 2 (pwHaar G) ℂ).comp (pwT0 (G := G) k)

/-- Integral formula for `T0` applied to a continuous function. -/
private theorem pwT0_toLp_apply (k k' : C(G, ℂ)) (g : G) :
    (pwT0Map (G := G) k (ContinuousMap.toLp 2 (pwHaar G) ℂ k')) g
      = ∫ h, k' h * k (h⁻¹ * g) ∂(pwHaar G) := by
  rw [pwT0Map_apply]
  change ⟪ContinuousMap.toLp 2 (pwHaar G) ℂ (pwPhiKer (G := G) k g),
    ContinuousMap.toLp 2 (pwHaar G) ℂ k'⟫ = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards with x
  simp only [pwPhiKer_apply]
  rw [Complex.conj_conj]

/-- Lipschitz estimate for values of `T0 f`. -/
private theorem pwT0_lipschitz (k : C(G, ℂ)) (f : Lp ℂ 2 (pwHaar G)) (g g' : G) :
    ‖(pwT0Map (G := G) k f) g - (pwT0Map (G := G) k f) g'‖
      ≤ ‖pwPhi (G := G) k g - pwPhi (G := G) k g'‖ * ‖f‖ := by
  rw [pwT0Map_apply, pwT0Map_apply, ← inner_sub_left]
  exact norm_inner_le_norm _ _

/-- The set of bounded versions of `T0 f` for `‖f‖ ≤ 1`. -/
private noncomputable def pwA (k : C(G, ℂ)) : Set (G →ᵇ ℂ) :=
  (ContinuousMap.isometryEquivBoundedOfCompact G ℂ) ''
    ((fun f => pwT0Map (G := G) k f) '' Metric.closedBall 0 1)

/-- Values of members of `pwA k` lie in the closed ball of radius `C`. -/
private theorem pwA_values (k : C(G, ℂ)) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ g : G, ‖pwPhi (G := G) k g‖ ≤ C) (Y : G →ᵇ ℂ) (hY : Y ∈ pwA (G := G) k)
    (x : G) : Y x ∈ Metric.closedBall (0 : ℂ) C := by
  obtain ⟨f, hfball, hfx⟩ := pwA_mem_obtain (G := G) k Y hY
  have hfnorm : ‖f‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp hfball
    rwa [dist_eq_norm, sub_zero] at h
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hfx]
  rw [pwT0Map_apply]
  calc ‖⟪pwPhi (G := G) k x, f⟫‖ ≤ ‖pwPhi (G := G) k x‖ * ‖f‖ :=
        norm_inner_le_norm _ _
    _ ≤ C * 1 := mul_le_mul (hC x) hfnorm (norm_nonneg _) hC0
    _ = C := mul_one _

/-- The family `pwA k` is equicontinuous. -/
private theorem pwA_equicontinuous (k : C(G, ℂ)) :
    Equicontinuous (fun x : ↥(pwA (G := G) k) => ⇑(↑x : G →ᵇ ℂ)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hcont : ContinuousAt (pwPhi (G := G) k) x₀ :=
    (pwPhi_continuous (G := G) k).continuousAt
  have hΦ : ∀ᶠ x : G in nhds x₀,
      dist (pwPhi (G := G) k x) (pwPhi (G := G) k x₀) < ε :=
    hcont.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hΦ] with x hx i
  obtain ⟨f, hfball, hfx⟩ := pwA_mem_obtain (G := G) k _ i.property
  have hfnorm : ‖f‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp hfball
    rwa [dist_eq_norm, sub_zero] at h
  have e1 : dist ((↑i : G →ᵇ ℂ) x₀) ((↑i : G →ᵇ ℂ) x)
      ≤ dist (pwPhi (G := G) k x₀) (pwPhi (G := G) k x) := by
    simp only [hfx]
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖(pwT0Map (G := G) k f) x₀ - (pwT0Map (G := G) k f) x‖
        ≤ ‖pwPhi (G := G) k x₀ - pwPhi (G := G) k x‖ * ‖f‖ :=
          pwT0_lipschitz (G := G) k f x₀ x
      _ ≤ ‖pwPhi (G := G) k x₀ - pwPhi (G := G) k x‖ * 1 :=
        mul_le_mul_of_nonneg_left hfnorm (norm_nonneg _)
      _ = ‖pwPhi (G := G) k x₀ - pwPhi (G := G) k x‖ := mul_one _
  calc dist ((↑i : G →ᵇ ℂ) x₀) ((↑i : G →ᵇ ℂ) x)
      ≤ dist (pwPhi (G := G) k x₀) (pwPhi (G := G) k x) := e1
    _ = dist (pwPhi (G := G) k x) (pwPhi (G := G) k x₀) := dist_comm _ _
    _ < ε := hx

/-- `T` is a compact operator, via Arzelà–Ascoli. -/
private theorem pwT_compact (k : C(G, ℂ)) :
    IsCompactOperator ⇑(pwT (G := G) k) := by
  obtain ⟨C, hC0, hC⟩ := pwPhi_bound (G := G) k
  have hA : ∀ Y : G →ᵇ ℂ, ∀ x : G, Y ∈ pwA (G := G) k →
      Y x ∈ Metric.closedBall (0 : ℂ) C :=
    fun Y x hY => pwA_values (G := G) k C hC0 hC Y hY x
  have hclosure : IsCompact (closure (pwA (G := G) k)) :=
    BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall 0 C) _ hA
      (pwA_equicontinuous (G := G) k)
  have hK : IsCompact (⇑(ContinuousMap.toLp 2 (pwHaar G) ℂ) ''
      (⇑(ContinuousMap.isometryEquivBoundedOfCompact G ℂ).symm ''
        closure (pwA (G := G) k))) :=
    (hclosure.image
      (ContinuousMap.isometryEquivBoundedOfCompact G ℂ).symm.continuous).image
      (ContinuousMap.toLp 2 (pwHaar G) ℂ).continuous
  have hTf : ∀ f : Lp ℂ 2 (pwHaar G),
      (pwT0 (G := G) k) f = pwT0Map (G := G) k f :=
    fun f => LinearMap.mkContinuousOfExistsBound_apply _ _ f
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall (0 : Lp ℂ 2 (pwHaar G)) 1,
    Metric.closedBall_mem_nhds 0 one_pos, _, hK, ?_⟩
  intro y hy
  obtain ⟨f, hfball, rfl⟩ := hy
  refine ⟨(pwT0 (G := G) k) f,
    ⟨(ContinuousMap.isometryEquivBoundedOfCompact G ℂ) (pwT0Map (G := G) k f),
      ?_, ?_⟩, rfl⟩
  · exact subset_closure ⟨pwT0Map (G := G) k f, ⟨f, hfball, rfl⟩, rfl⟩
  · rw [IsometryEquiv.symm_apply_apply]
    exact (hTf f).symm

/-- `T` commutes with every left translation. -/
private theorem pwT_comm (k : C(G, ℂ)) (a : G) (f : Lp ℂ 2 (pwHaar G)) :
    (pwT (G := G) k) (pwTransl (G := G) a f)
      = pwTransl (G := G) a ((pwT (G := G) k) f) := by
  have hT0eq : pwT0Map (G := G) k (pwTransl (G := G) a f)
      = (pwT0Map (G := G) k f).comp ⟨fun t => a⁻¹ * t, continuous_const_mul a⁻¹⟩ := by
    apply ContinuousMap.ext
    intro g
    simp only [ContinuousMap.comp_apply, pwT0Map_apply]
    change ⟪pwPhi (G := G) k g, pwTransl (G := G) a f⟫
      = ⟪pwPhi (G := G) k (a⁻¹ * g), f⟫
    rw [pwTransl_inner' (G := G) a _ f, pwTransl_Phi (G := G) k a g]
  have hTf : ∀ x : Lp ℂ 2 (pwHaar G),
      (pwT0 (G := G) k) x = pwT0Map (G := G) k x :=
    fun x => LinearMap.mkContinuousOfExistsBound_apply _ _ x
  have hTT : ∀ x : Lp ℂ 2 (pwHaar G),
      (pwT (G := G) k) x
        = ContinuousMap.toLp 2 (pwHaar G) ℂ ((pwT0 (G := G) k) x) := fun x => rfl
  rw [hTT, hTT, hTf, hTf, hT0eq, ← pwTransl_toLp]

/-- `S` is `T† ∘L T`. -/
private noncomputable def pwS (k : C(G, ℂ)) :
    (Lp ℂ 2 (pwHaar G)) →L[ℂ] Lp ℂ 2 (pwHaar G) :=
  (ContinuousLinearMap.adjoint (pwT (G := G) k)).comp (pwT (G := G) k)

/-- `S` is compact. -/
private theorem pwS_compact (k : C(G, ℂ)) :
    IsCompactOperator ⇑(pwS (G := G) k) := by
  have h := (pwT_compact (G := G) k).clm_comp
    (ContinuousLinearMap.adjoint (pwT (G := G) k))
  have hfun : (⇑(ContinuousLinearMap.adjoint (pwT (G := G) k)) ∘ ⇑(pwT (G := G) k))
      = ⇑(pwS (G := G) k) :=
    funext fun _ => rfl
  rwa [hfun] at h

/-- The adjoint of `T` commutes with every translation. -/
private theorem pwAdj_comm (k : C(G, ℂ)) (a : G) (u : Lp ℂ 2 (pwHaar G)) :
    (ContinuousLinearMap.adjoint (pwT (G := G) k)) (pwTransl (G := G) a u)
      = pwTransl (G := G) a
        ((ContinuousLinearMap.adjoint (pwT (G := G) k)) u) := by
  apply ext_inner_right ℂ
  intro v
  calc ⟪(ContinuousLinearMap.adjoint (pwT (G := G) k)) (pwTransl (G := G) a u), v⟫
        = ⟪pwTransl (G := G) a u, (pwT (G := G) k) v⟫ :=
          ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪u, pwTransl (G := G) a⁻¹ ((pwT (G := G) k) v)⟫ :=
          pwTransl_inner (G := G) a _ _
      _ = ⟪u, (pwT (G := G) k) (pwTransl (G := G) a⁻¹ v)⟫ := by
          rw [pwT_comm]
      _ = ⟪(ContinuousLinearMap.adjoint (pwT (G := G) k)) u,
            pwTransl (G := G) a⁻¹ v⟫ :=
          (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
      _ = ⟪pwTransl (G := G) a
            ((ContinuousLinearMap.adjoint (pwT (G := G) k)) u), v⟫ :=
          (pwTransl_inner (G := G) a _ _).symm

/-- `S` commutes with every translation. -/
private theorem pwS_comm (k : C(G, ℂ)) (a : G) (f : Lp ℂ 2 (pwHaar G)) :
    (pwS (G := G) k) (pwTransl (G := G) a f)
      = pwTransl (G := G) a ((pwS (G := G) k) f) := by
  unfold pwS
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    pwT_comm, pwAdj_comm]

/-- Eigenspaces of `S` are invariant under every translation. -/
private theorem pwEigen_invariant (k : C(G, ℂ)) (c : ℂ) (a : G)
    (v : Lp ℂ 2 (pwHaar G))
    (hv : v ∈ Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c) :
    pwTransl (G := G) a v ∈ Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hcomm : ((pwS (G := G) k) : Module.End ℂ (Lp ℂ 2 (pwHaar G)))
        (pwTransl (G := G) a v)
      = pwTransl (G := G) a (((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) v) :=
    pwS_comm (G := G) k a v
  rw [hcomm, hv, map_smul]

/-- Matrix coefficients on a nonzero eigenspace are continuous in `g`
(`u` is arbitrary; only `v`'s eigenvalue equation is used). -/
private theorem pwEigen_coeff_continuous (k : C(G, ℂ)) (c : ℂ) (hc : c ≠ 0)
    (u v : Lp ℂ 2 (pwHaar G))
    (hv : v ∈ Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c) :
    Continuous (fun g => ⟪u, pwTransl (G := G) g v⟫) := by
  rw [Module.End.mem_eigenspace_iff] at hv
  have hv' : (pwS (G := G) k) v = c • v := hv
  have hvc : v = c⁻¹ • ((pwS (G := G) k) v) := by
    rw [hv', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hSv : (pwS (G := G) k) v
      = (ContinuousLinearMap.adjoint (pwT (G := G) k)) ((pwT (G := G) k) v) :=
    rfl
  have hfun : (fun g => ⟪u, pwTransl (G := G) g v⟫)
      = fun g => c⁻¹ * ⟪(pwT (G := G) k) u,
        pwTransl (G := G) g ((pwT (G := G) k) v)⟫ := by
    funext g
    conv_lhs => rw [hvc, map_smul, inner_smul_right, hSv, ← pwAdj_comm,
      ContinuousLinearMap.adjoint_inner_right]
  have hTvc : (pwT (G := G) k) v
      = ContinuousMap.toLp 2 (pwHaar G) ℂ ((pwT0 (G := G) k) v) := rfl
  rw [hfun, hTvc]
  exact continuous_const.mul
    (continuous_const.inner (pwTransl_toLp_continuous (G := G) _))

/-- (helper) If `z` fixes every vector of every eigenspace of `S`,
then `z` fixes every value of `S`. -/
private theorem pwSep_fixS (z : G) (k : C(G, ℂ))
    (hall : ∀ (c : ℂ), c ≠ 0 → ∀ (v : Lp ℂ 2 (pwHaar G)),
      v ∈ Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) c →
      pwTransl (G := G) z v = v) :
    ∀ w : Lp ℂ 2 (pwHaar G),
      pwTransl (G := G) z ((pwS (G := G) k) w) = (pwS (G := G) k) w := by
  set B : (Lp ℂ 2 (pwHaar G)) →L[ℂ] Lp ℂ 2 (pwHaar G) :=
    ((pwTransl (G := G) z).toContinuousLinearMap - ContinuousLinearMap.id ℂ _) ∘L
      (pwS (G := G) k) with hBdef
  have eLz : ∀ x : Lp ℂ 2 (pwHaar G),
      ((pwTransl (G := G) z).toContinuousLinearMap) ((pwS (G := G) k) x)
        = (pwTransl (G := G) z) ((pwS (G := G) k) x) := fun _ => rfl
  have hBv : ∀ v : Lp ℂ 2 (pwHaar G), B v
      = (pwTransl (G := G) z) ((pwS (G := G) k) v)
        - ((pwS (G := G) k) v) := by
    intro v
    rw [hBdef, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, eLz]
  have hsub : ∀ μ : ℂ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ ≤ LinearMap.ker
        ((B : Lp ℂ 2 (pwHaar G) →ₗ[ℂ] Lp ℂ 2 (pwHaar G))) := by
    intro μ v hv
    have hvmem := hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have hv' : (pwS (G := G) k) v = μ • v := hv
    rw [LinearMap.mem_ker]
    change B v = 0
    rw [hBv, hv']
    by_cases hμ : μ = 0
    · subst hμ
      simp
    · rw [map_smul, hall μ hμ v hvmem, sub_self]
  have hiSup : (⨆ μ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ) ≤ LinearMap.ker
      ((B : Lp ℂ 2 (pwHaar G) →ₗ[ℂ] Lp ℂ 2 (pwHaar G))) :=
    iSup_le hsub
  have hclosed : IsClosed ((LinearMap.ker
      ((B : Lp ℂ 2 (pwHaar G) →ₗ[ℂ] Lp ℂ 2 (pwHaar G))) : Submodule ℂ _) :
      Set (Lp ℂ 2 (pwHaar G))) :=
    ContinuousLinearMap.isClosed_ker B
  have htop : ((⨆ μ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff]
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      (pwS_compact (G := G) k) (pwS_symmetric (G := G) k)
  intro w
  have hmem : w ∈ ((⨆ μ, Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) μ)).topologicalClosure := by
    rw [htop]
    exact Submodule.mem_top
  have hkerw := Submodule.topologicalClosure_minimal _ hiSup hclosed hmem
  have hkerw' : B w = 0 := hkerw
  rw [hBv, sub_eq_zero] at hkerw'
  exact hkerw'

/-- Some nonzero eigenspace of `S` moves under translation by `z`. -/
private theorem pwSeparation (z : G) (k : C(G, ℂ))
    (hi : ∫ h, k h * k (h⁻¹) ∂(pwHaar G) ≠ 0)
    (hii : ∀ h : G, k h * k (h⁻¹ * z⁻¹) = 0) :
    ∃ (c : ℂ) (_hc : c ≠ 0) (v : Lp ℂ 2 (pwHaar G)),
      v ∈ Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) c ∧ pwTransl (G := G) z v ≠ v := by
  by_contra hall
  have hall' : ∀ (c : ℂ), c ≠ 0 → ∀ (v : Lp ℂ 2 (pwHaar G)),
      v ∈ Module.End.eigenspace ((pwS (G := G) k) :
        Module.End ℂ (Lp ℂ 2 (pwHaar G))) c →
      pwTransl (G := G) z v = v := by
    intro c hc v hvmem
    by_contra hne
    exact hall ⟨c, hc, v, hvmem, hne⟩
  have hfixS := pwSep_fixS (G := G) z k hall'
  have hS0 : ∀ w : Lp ℂ 2 (pwHaar G),
      (pwS (G := G) k) (pwTransl (G := G) z w - w) = 0 := by
    intro w
    rw [map_sub, pwS_comm, hfixS, sub_self]
  set ψ : Lp ℂ 2 (pwHaar G) := ContinuousMap.toLp 2 (pwHaar G) ℂ k with hψdef
  have hw0 := hS0 ψ
  have hnorm : ‖(pwT (G := G) k) (pwTransl (G := G) z ψ - ψ)‖ ^ 2 = 0 := by
    have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left
      (pwT (G := G) k) (pwTransl (G := G) z ψ - ψ)
    have e : ((ContinuousLinearMap.adjoint (pwT (G := G) k)) ∘L
        (pwT (G := G) k)) (pwTransl (G := G) z ψ - ψ)
        = (pwS (G := G) k) (pwTransl (G := G) z ψ - ψ) := rfl
    rw [e, hw0, inner_zero_left] at h
    simpa using h
  have hT0 : (pwT (G := G) k) (pwTransl (G := G) z ψ - ψ) = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hnorm)
  have hTeq : (pwT (G := G) k) (pwTransl (G := G) z ψ)
      = (pwT (G := G) k) ψ := by
    have hms := map_sub (pwT (G := G) k) (pwTransl (G := G) z ψ) ψ
    rw [hT0] at hms
    exact sub_eq_zero.mp hms.symm
  have hLz : pwTransl (G := G) z ((pwT (G := G) k) ψ)
      = (pwT (G := G) k) ψ := by
    rw [← pwT_comm]
    exact hTeq
  have hTTψ : (pwT (G := G) k) ψ
      = ContinuousMap.toLp 2 (pwHaar G) ℂ ((pwT0 (G := G) k) ψ) := rfl
  have hT0ψ : (pwT0 (G := G) k) ψ = pwT0Map (G := G) k ψ :=
    LinearMap.mkContinuousOfExistsBound_apply _ _ _
  rw [hTTψ, hT0ψ, pwTransl_toLp] at hLz
  have hCeq := (ContinuousMap.toLp_inj (pwHaar G)).mp hLz
  have h1 := congrArg (fun F : C(G, ℂ) => F 1) hCeq
  rw [ContinuousMap.comp_apply] at h1
  change (pwT0Map (G := G) k ψ) (z⁻¹ * 1) = (pwT0Map (G := G) k ψ) 1 at h1
  rw [mul_one, hψdef, pwT0_toLp_apply, pwT0_toLp_apply] at h1
  have hz : (∫ h, k h * k (h⁻¹ * z⁻¹) ∂(pwHaar G)) = 0 := by
    simp only [hii, integral_zero]
  have h1' : (∫ h, k h * k (h⁻¹ * 1) ∂(pwHaar G))
      = ∫ h, k h * k h⁻¹ ∂(pwHaar G) := by
    apply integral_congr_ae
    filter_upwards with h
    rw [mul_one]
  rw [hz, h1'] at h1
  exact hi h1.symm

/-- Restriction of translation to an invariant submodule. -/
private noncomputable def pwU (E : Submodule ℂ (Lp ℂ 2 (pwHaar G)))
    (hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
      v ∈ E → pwTransl (G := G) g v ∈ E)
    (g : G) : Module.End ℂ ↥E :=
  LinearMap.restrict ((pwTransl (G := G) g).toLinearMap) (fun v hv => hinv g v hv)
end PWHelpers

/--
For a compact Hausdorff topological group and `x ≠ y`, there exist `n>0` and a continuous
homomorphism `ρ : G → Matrix (Fin n) (Fin n) ℂ` with `ρ g ∈ unitaryGroup` for all `g`, `ρ 1 = 1`,
and `ρ x ≠ ρ y`. Source: F. Peter and H. Weyl, Math. Ann. 97 (1927), 737–755; Folland, A Course in
Abstract Harmonic Analysis 2nd ed.; Knapp, Lie Groups Beyond an Introduction 2nd ed.

Proves `Wanted` entry `peter_weyl_point_separation`.
-/
theorem peter_weyl_point_separation
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    {x y : G} (hxy : x ≠ y) :
    ∃ (n : ℕ) (_hn : 0 < n) (ρ : G → Matrix (Fin n) (Fin n) ℂ),
      Continuous ρ ∧
      ρ 1 = 1 ∧
      (∀ g h : G, ρ (g * h) = ρ g * ρ h) ∧
      (∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
      ρ x ≠ ρ y := by
  borelize G
  have hz : x⁻¹ * y ≠ 1 := by
    intro h
    exact hxy (inv_mul_eq_one.mp h)
  obtain ⟨k, hi, hii⟩ := pwBump (G := G) hz
  obtain ⟨c, hc, v₀, hmem, hne⟩ := pwSeparation (G := G) (x⁻¹ * y) k hi hii
  set E : Submodule ℂ (Lp ℂ 2 (pwHaar G)) :=
    Module.End.eigenspace ((pwS (G := G) k) :
      Module.End ℂ (Lp ℂ 2 (pwHaar G))) c with hEdef
  have hfin : FiniteDimensional ℂ ↥E :=
    ContinuousLinearMap.finite_dimensional_eigenspace (pwS_compact (G := G) k) c hc
  have hinv : ∀ (g : G) (v : Lp ℂ 2 (pwHaar G)),
      v ∈ E → pwTransl (G := G) g v ∈ E := by
    intro g v hv
    exact pwEigen_invariant (G := G) k c g v hv
  have hcont : ∀ (u v : ↥E), Continuous fun g =>
      ⟪(u : Lp ℂ 2 (pwHaar G)), pwTransl (G := G) g (v : Lp ℂ 2 (pwHaar G))⟫ := by
    intro u v
    exact pwEigen_coeff_continuous (G := G) k c hc
      (u : Lp ℂ 2 (pwHaar G)) (v : Lp ℂ 2 (pwHaar G)) v.property
  obtain ⟨n, hn, ρ, hρc, hρ1, hρm, hρu, hρz⟩ :=
    pwRep (G := G) E hfin hinv hcont (x⁻¹ * y) ⟨v₀, hmem⟩ hne
  refine ⟨n, hn, ρ, hρc, hρ1, hρm, hρu, ?_⟩
  intro hxy'
  apply hρz
  rw [hρm x⁻¹ y, ← hxy', ← hρm, inv_mul_cancel, hρ1]

end MathlibExt.Topology.Algebra.PeterWeylWanted
