/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Def.Analysis.CStarAlgebra.KaplanskyDensity
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapPlumbing

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kapToBounded_ofBounded (T : H →L[ℂ] H) :
    toBounded (kapOfBounded T) = T :=
  LinearEquiv.symm_apply_apply _ T

theorem kapOfBounded_toBounded (p : H →Lₚₜ[ℂ] H) :
    kapOfBounded (toBounded p) = p :=
  LinearEquiv.apply_symm_apply _ p

theorem kapToBounded_apply (p : H →Lₚₜ[ℂ] H) (v : H) :
    (toBounded p) v = p v :=
  ContinuousLinearMap.toUniformConvergenceCLM_symm_apply

omit [CompleteSpace H] in
theorem kapOfBounded_apply (T : H →L[ℂ] H) (v : H) :
    (kapOfBounded T) v = T v :=
  ContinuousLinearMap.toUniformConvergenceCLM_apply

theorem kapToBounded_add (p q : H →Lₚₜ[ℂ] H) :
    toBounded (p + q) = toBounded p + toBounded q :=
  map_add _ _ _

theorem kapToBounded_smul (c : ℂ) (p : H →Lₚₜ[ℂ] H) :
    toBounded (c • p) = c • toBounded p :=
  map_smul _ _ _

theorem kapToBounded_zero : toBounded (0 : H →Lₚₜ[ℂ] H) = 0 :=
  map_zero _

omit [CompleteSpace H] in
theorem kapOfBounded_add (T U : H →L[ℂ] H) :
    kapOfBounded (T + U) = kapOfBounded T + kapOfBounded U :=
  map_add _ _ _

omit [CompleteSpace H] in
theorem kapOfBounded_smul (c : ℂ) (T : H →L[ℂ] H) :
    kapOfBounded (c • T) = c • kapOfBounded T :=
  map_smul _ _ _

omit [CompleteSpace H] in
theorem kapOfBounded_zero : kapOfBounded (0 : H →L[ℂ] H) = 0 :=
  map_zero _

omit [CompleteSpace H] in
theorem kapReal_smul_sot (r : ℝ) (p : H →Lₚₜ[ℂ] H) :
    r • p = (r : ℂ) • p :=
  RCLike.real_smul_eq_coe_smul r p

omit [CompleteSpace H] in
theorem kapReal_smul_clm (r : ℝ) (T : H →L[ℂ] H) :
    r • T = (r : ℂ) • T :=
  RCLike.real_smul_eq_coe_smul r T

theorem kapToBounded_real_smul (r : ℝ) (p : H →Lₚₜ[ℂ] H) :
    toBounded (r • p) = r • toBounded p := by
  rw [kapReal_smul_sot, kapReal_smul_clm, kapToBounded_smul]

omit [CompleteSpace H] in
/-- `ofBounded` is continuous from the norm topology to SOT. -/
theorem kapOfBounded_continuous :
    Continuous (kapOfBounded : (H →L[ℂ] H) → H →Lₚₜ[ℂ] H) :=
  (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H).continuous

omit [CompleteSpace H] in
/-- Evaluation at a vector is SOT-continuous. -/
theorem kapEval_continuous (v : H) :
    Continuous (fun p : H →Lₚₜ[ℂ] H => p v) :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H v).continuous

theorem kapToBounded_star (p : H →Lₚₜ[ℂ] H) :
    toBounded (kapStar p) = star (toBounded p) :=
  kapToBounded_ofBounded _

theorem kapStar_add (p q : H →Lₚₜ[ℂ] H) :
    kapStar (p + q) = kapStar p + kapStar q := by
  unfold kapStar
  rw [kapToBounded_add, star_add, kapOfBounded_add]

theorem kapStar_real_smul (r : ℝ) (p : H →Lₚₜ[ℂ] H) :
    kapStar (r • p) = r • kapStar p := by
  unfold kapStar
  rw [kapToBounded_real_smul, kapReal_smul_clm r (toBounded p), star_smul]
  have hstar : star (r : ℂ) = (r : ℂ) := RCLike.conj_ofReal r
  rw [hstar, kapOfBounded_smul, ← kapReal_smul_sot]

theorem kapStar_kapStar (p : H →Lₚₜ[ℂ] H) :
    kapStar (kapStar p) = p := by
  unfold kapStar
  rw [kapToBounded_ofBounded, star_star, kapOfBounded_toBounded]

theorem kapStar_eq_iff (p : H →Lₚₜ[ℂ] H) :
    kapStar p = p ↔ IsSelfAdjoint (toBounded p) := by
  constructor
  · intro h
    rw [isSelfAdjoint_iff]
    have h2 := congrArg toBounded h
    rwa [kapToBounded_star] at h2
  · intro h
    unfold kapStar
    rw [h.star_eq, kapOfBounded_toBounded]

omit [CompleteSpace H] in
theorem kapOfBounded_mul_post (T U : H →L[ℂ] H) :
    kapOfBounded (T * U) =
      PointwiseConvergenceCLM.postcomp H T (kapOfBounded U) := by
  rw [ContinuousLinearMap.mul_def]
  rfl

omit [CompleteSpace H] in
theorem kapOfBounded_mul_pre (T U : H →L[ℂ] H) :
    kapOfBounded (T * U) =
      PointwiseConvergenceCLM.precomp H U (kapOfBounded T) := by
  rw [ContinuousLinearMap.mul_def]
  rfl

/-- The SOT unit ball is SOT-closed. -/
theorem kapIsClosed_ball :
    IsClosed {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} := by
  have hset : {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1} = ⋂ v : H, {p | ‖p v‖ ≤ ‖v‖} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [ContinuousLinearMap.opNorm_le_iff zero_le_one]
    constructor
    · intro h v
      calc ‖p v‖ = ‖(toBounded p) v‖ := by rw [kapToBounded_apply]
        _ ≤ 1 * ‖v‖ := h v
        _ = ‖v‖ := one_mul _
    · intro h v
      calc ‖(toBounded p) v‖ = ‖p v‖ := by rw [kapToBounded_apply]
        _ ≤ 1 * ‖v‖ := by rw [one_mul]; exact h v
  rw [hset]
  exact isClosed_iInter fun v =>
    isClosed_le (continuous_norm.comp (kapEval_continuous v)) continuous_const

end KapPlumbing

section KapDual

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every SOT-continuous linear functional is a finite sum of vector functionals. -/
theorem kapExists_sum_inner (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    ∃ (s : Finset H) (w : ↥s → H), ∀ p : H →Lₚₜ[ℂ] H,
      f p = ∑ x : ↥s, inner ℂ (w x) (p (x : H)) := by
  classical
  have hqq : ∀ p : H →Lₚₜ[ℂ] H,
      (normSeminorm ℂ ℂ).comp (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ) p
      = ‖f p‖ := by
    intro p
    simp [Seminorm.comp_apply, coe_normSeminorm]
  have hqcont : Continuous
      ⇑((normSeminorm ℂ ℂ).comp (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ)) := by
    have hfun : ⇑((normSeminorm ℂ ℂ).comp (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ))
        = fun p => ‖f p‖ := funext hqq
    rw [hfun]
    exact continuous_norm.comp f.cont
  obtain ⟨s, C, hC0, hC⟩ := Seminorm.bound_of_continuous
    (PointwiseConvergenceCLM.withSeminorms :
      WithSeminorms (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H))
    _ hqcont
  set Φ : (H →Lₚₜ[ℂ] H) →ₗ[ℂ] (↥s → H) :=
    LinearMap.pi fun x : ↥s =>
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H (x : H)).toLinearMap with hΦdef
  have hΦapply : ∀ (p : H →Lₚₜ[ℂ] H) (x : ↥s), Φ p x = p (x : H) := fun p x => rfl
  have hfam : ∀ (x : H) (p : H →Lₚₜ[ℂ] H),
      (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H) x p = ‖p x‖ :=
    fun x p => rfl
  have hsup : ∀ p : H →Lₚₜ[ℂ] H,
      (C • s.sup (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H)) p
        ≤ (C : ℝ) * ‖Φ p‖ := by
    intro p
    rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg C)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun x hx => ?_
    rw [hfam]
    calc ‖p x‖ = ‖Φ p ⟨x, hx⟩‖ := by rw [hΦapply]
      _ ≤ ‖Φ p‖ := norm_le_pi_norm _ _
  have hbound : ∀ p : H →Lₚₜ[ℂ] H, ‖f p‖ ≤ (C : ℝ) * ‖Φ p‖ := by
    intro p
    calc ‖f p‖ = ((normSeminorm ℂ ℂ).comp
            (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ)) p := (hqq p).symm
      _ ≤ (C • s.sup
            (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H)) p :=
          Seminorm.le_def.mp hC p
      _ ≤ (C : ℝ) * ‖Φ p‖ := hsup p
  have hker : LinearMap.ker Φ ≤
      LinearMap.ker (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ) := by
    intro p hp
    rw [LinearMap.mem_ker] at hp
    rw [LinearMap.mem_ker]
    have hb := hbound p
    rw [hp, norm_zero, mul_zero] at hb
    have hfp : f p = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    exact hfp
  set g₀ : LinearMap.range Φ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker Φ).liftQ (↑f : (H →Lₚₜ[ℂ] H) →ₛₗ[RingHom.id ℂ] ℂ) hker).comp
      (LinearMap.quotKerEquivRange Φ).symm.toLinearMap with hg₀def
  have hg₀apply : ∀ (p : H →Lₚₜ[ℂ] H) (h : Φ p ∈ LinearMap.range Φ),
      g₀ ⟨Φ p, h⟩ = f p := by
    intro p h
    rw [hg₀def, LinearMap.comp_apply]
    have hsymm : ((LinearMap.quotKerEquivRange Φ).symm.toLinearMap) ⟨Φ p, h⟩
        = (LinearMap.ker Φ).mkQ p :=
      LinearMap.quotKerEquivRange_symm_apply_image Φ p h
    rw [hsymm, Submodule.mkQ_apply]
    exact Submodule.liftQ_apply _ _ _
  have hg₀bound : ∀ v : LinearMap.range Φ, ‖g₀ v‖ ≤ (C : ℝ) * ‖v‖ := by
    intro v
    obtain ⟨p, hp⟩ := v.property
    have hmem2 : Φ p ∈ LinearMap.range Φ := ⟨p, rfl⟩
    have hv : v = ⟨Φ p, hmem2⟩ := Subtype.ext hp.symm
    rw [hv, hg₀apply, ← Submodule.norm_coe]
    exact hbound p
  obtain ⟨G, hG, -⟩ := exists_extension_norm_eq (LinearMap.range Φ)
    (LinearMap.mkContinuous g₀ (C : ℝ) hg₀bound)
  have hfp : ∀ p : H →Lₚₜ[ℂ] H, f p = G (Φ p) := by
    intro p
    have hmem : Φ p ∈ LinearMap.range Φ := ⟨p, rfl⟩
    have e1 : G (Φ p) = (LinearMap.mkContinuous g₀ (C : ℝ) hg₀bound) ⟨Φ p, hmem⟩ :=
      hG ⟨Φ p, hmem⟩
    have e2 : (LinearMap.mkContinuous g₀ (C : ℝ) hg₀bound) ⟨Φ p, hmem⟩ = f p := by
      rw [LinearMap.mkContinuous_apply]
      exact hg₀apply _ _
    exact e2.symm.trans e1.symm
  refine ⟨s, fun x => (InnerProductSpace.toDual ℂ H).symm
    (ContinuousLinearMap.comp G
      (ContinuousLinearMap.single ℂ (fun _ : ↥s => H) x)), fun p => ?_⟩
  rw [hfp p, ← ContinuousLinearMap.sum_comp_single ℂ _ G (Φ p)]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (InnerProductSpace.toDual_symm_apply).symm

end KapDual

section KapStarCont

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Precomposition with `kapStar` preserves SOT-continuity of functionals. -/
theorem kapContinuous_starApply (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    Continuous fun p : H →Lₚₜ[ℂ] H => f (kapStar p) := by
  obtain ⟨s, w, hw⟩ := kapExists_sum_inner f
  have hfun : (fun p : H →Lₚₜ[ℂ] H => f (kapStar p))
      = fun p => ∑ x : ↥s, inner ℂ (p (w x)) ((x : H)) := by
    funext p
    rw [hw]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold kapStar
    rw [kapOfBounded_apply, ContinuousLinearMap.star_eq_adjoint]
    have hadj : inner ℂ (w x) ((ContinuousLinearMap.adjoint (toBounded p)) ↑x)
        = inner ℂ ((toBounded p) (w x)) ↑x :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    rw [hadj, kapToBounded_apply]
  rw [hfun]
  exact continuous_finsetSum _ fun x _ => (kapEval_continuous (w x)).inner continuous_const

/-- Real part of `f` after `kapStar` is continuous. -/
theorem kapContinuous_re_starApply (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    Continuous fun p : H →Lₚₜ[ℂ] H => Complex.re (f (kapStar p)) :=
  Complex.continuous_re.comp (kapContinuous_starApply f)

/-- Sum of real parts before and after `kapStar` is continuous. -/
theorem kapContinuous_re_add (f : StrongDual ℂ (H →Lₚₜ[ℂ] H)) :
    Continuous fun p : H →Lₚₜ[ℂ] H => Complex.re (f p) + Complex.re (f (kapStar p)) :=
  (Complex.continuous_re.comp f.cont).add (kapContinuous_re_starApply f)

end KapStarCont

section KapConvex

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The SOT-closure of a convex `kapStar`-invariant set is `kapStar`-invariant. -/
theorem kapStar_mem_closure_of_convex {C : Set (H →Lₚₜ[ℂ] H)}
    (hconv : Convex ℝ C) (hstar : ∀ p ∈ C, kapStar p ∈ C)
    {q : H →Lₚₜ[ℂ] H} (hq : q ∈ closure C) :
    kapStar q ∈ closure C := by
  by_contra hmem
  let : ContinuousSMul ℂ (H →Lₚₜ[ℂ] H) :=
    WithSeminorms.continuousSMul (PointwiseConvergenceCLM.withSeminorms :
      WithSeminorms (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H))
  obtain ⟨f, u, hlt, hgt⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    hconv.closure isClosed_closure hmem
  have hle : ∀ p ∈ C, u ≤ RCLike.re (f (kapStar p)) := by
    intro p hp
    exact le_of_lt (hgt _ (subset_closure (hstar p hp)))
  have hcont : Continuous fun p : H →Lₚₜ[ℂ] H => RCLike.re (f (kapStar p)) := by
    simpa only [RCLike.re_to_complex] using kapContinuous_re_starApply f
  have hclosed : IsClosed {p : H →Lₚₜ[ℂ] H | u ≤ RCLike.re (f (kapStar p))} :=
    isClosed_le continuous_const hcont
  have hqle : u ≤ RCLike.re (f (kapStar q)) :=
    closure_minimal (fun p hp => hle p hp) hclosed hq
  exact (not_le.mpr hlt) hqle

/-- Fixed points of `kapStar` in the closure are limits of fixed points. -/
theorem kapMem_closure_fixed_of_convex {C : Set (H →Lₚₜ[ℂ] H)}
    (hconv : Convex ℝ C) (hstar : ∀ p ∈ C, kapStar p ∈ C)
    {y : H →Lₚₜ[ℂ] H} (hy : y ∈ closure C) (hyy : kapStar y = y) :
    y ∈ closure {p : H →Lₚₜ[ℂ] H | p ∈ C ∧ kapStar p = p} := by
  by_contra hmem
  let : ContinuousSMul ℂ (H →Lₚₜ[ℂ] H) :=
    WithSeminorms.continuousSMul (PointwiseConvergenceCLM.withSeminorms :
      WithSeminorms (PointwiseConvergenceCLM.seminormFamily (RingHom.id ℂ) H H))
  have hconv_sa : Convex ℝ {p : H →Lₚₜ[ℂ] H | p ∈ C ∧ kapStar p = p} := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hpp, hppstar⟩ := hp
    obtain ⟨hqq, hqqstar⟩ := hq
    refine ⟨hconv hpp hqq ha hb hab, ?_⟩
    rw [kapStar_add, kapStar_real_smul, kapStar_real_smul, hppstar, hqqstar]
  obtain ⟨f, u, hlt, hgt⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    hconv_sa.closure isClosed_closure hmem
  have hmem_sa : ∀ p ∈ C, ((1/2 : ℝ) • (p + kapStar p))
      ∈ {p : H →Lₚₜ[ℂ] H | p ∈ C ∧ kapStar p = p} := by
    intro p hp
    refine ⟨?_, ?_⟩
    · have h1 : ((1/2 : ℝ) • (p + kapStar p))
          = (1/2 : ℝ) • p + (1/2 : ℝ) • kapStar p := smul_add _ _ _
      rw [h1]
      exact hconv hp (hstar p hp) (by norm_num) (by norm_num) (by norm_num)
    · rw [kapStar_real_smul, kapStar_add, kapStar_kapStar, add_comm (kapStar p) p]
  have hval : ∀ p : H →Lₚₜ[ℂ] H, RCLike.re (f ((1/2 : ℝ) • (p + kapStar p)))
      = (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p))) := by
    intro p
    have eC : Complex.re (f ((1/2 : ℝ) • (p + kapStar p)))
        = (1/2 : ℝ) * (Complex.re (f p) + Complex.re (f (kapStar p))) := by
      have e : f ((1/2 : ℝ) • (p + kapStar p))
          = (((1/2 : ℝ) : ℂ)) * (f p + f (kapStar p)) := by
        rw [kapReal_smul_sot, map_smul, map_add, smul_eq_mul]
      rw [e, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simpa only [RCLike.re_to_complex] using eC
  have hle : ∀ p ∈ C,
      u ≤ (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p))) := by
    intro p hp
    have h2 := hgt _ (subset_closure (hmem_sa p hp))
    rw [hval] at h2
    exact le_of_lt h2
  have hcont : Continuous fun p : H →Lₚₜ[ℂ] H =>
      (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p))) := by
    have h2 : Continuous fun p : H →Lₚₜ[ℂ] H =>
        (1/2 : ℝ) * (Complex.re (f p) + Complex.re (f (kapStar p))) :=
      continuous_const.mul (kapContinuous_re_add f)
    simpa only [← RCLike.re_to_complex] using h2
  have hclosed : IsClosed {p : H →Lₚₜ[ℂ] H |
      u ≤ (1/2 : ℝ) * (RCLike.re (f p) + RCLike.re (f (kapStar p)))} :=
    isClosed_le continuous_const hcont
  have hy_le : u ≤ (1/2 : ℝ) * (RCLike.re (f y) + RCLike.re (f (kapStar y))) :=
    closure_minimal (fun p hp => hle p hp) hclosed hy
  rw [hyy] at hy_le
  have hhalf : (1/2 : ℝ) * (RCLike.re (f y) + RCLike.re (f y))
      = RCLike.re (f y) := by
    ring
  rw [hhalf] at hy_le
  exact (not_le.mpr hlt) hy_le

end KapConvex
end Analysis.CStarAlgebra.KaplanskyDensityWanted
