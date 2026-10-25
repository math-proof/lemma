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
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part4
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapCayley

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kapR_cont : Continuous kapR := by
  unfold kapR
  refine Continuous.inv₀ (by continuity) (fun t => ?_)
  exact ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2)

theorem kapF_cont : Continuous kapF := by
  unfold kapF
  refine Continuous.div (by continuity) (by continuity) (fun t => ?_)
  exact ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2)

theorem kapMul_cont : Continuous (fun t : ℝ => t * kapR t) :=
  continuous_id.mul kapR_cont

theorem kapMulR_cont : Continuous (fun t : ℝ => kapR t * t) :=
  kapR_cont.mul continuous_id

theorem kapR_nonneg (t : ℝ) : 0 ≤ kapR t := by
  unfold kapR
  exact le_of_lt (inv_pos.mpr (by positivity : (0 : ℝ) < 1 + t ^ 2))

theorem kapR_le_one (t : ℝ) : kapR t ≤ 1 := by
  unfold kapR
  refine inv_le_one_of_one_le₀ ?_
  have h : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  linarith

theorem kapF_abs_le_one (t : ℝ) : |kapF t| ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h := two_mul_le_add_sq (|t|) (1 : ℝ)
  rw [mul_one, one_pow, sq_abs] at h
  have hab : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  unfold kapF
  rw [abs_div, abs_of_pos hpos, div_le_one hpos, hab]
  linarith

/-- The resolvent cfc has norm at most one. -/
theorem kapNorm_cfcR_le (a : H →L[ℂ] H) :
    ‖kapCfcR a‖ ≤ 1 := by
  unfold kapCfcR
  refine norm_cfc_le zero_le_one (fun t _ => ?_)
  calc ‖kapR t‖ = |kapR t| := Real.norm_eq_abs _
    _ = kapR t := abs_of_nonneg (kapR_nonneg t)
    _ ≤ 1 := kapR_le_one t

/-- The Cayley cfc has norm at most one. -/
theorem kapNorm_cfcF_le (a : H →L[ℂ] H) :
    ‖kapCfcF a‖ ≤ 1 := by
  unfold kapCfcF
  refine norm_cfc_le zero_le_one (fun t _ => ?_)
  calc ‖kapF t‖ = |kapF t| := Real.norm_eq_abs _
    _ ≤ 1 := kapF_abs_le_one t

theorem kapCfc_sq (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => t * t) a = a * a := by
  have h2 := cfc_pow_id (R := ℝ) (a := a) (n := 2) (ha := ha)
  have e : (fun t : ℝ => t * t) = (· ^ 2 : ℝ → ℝ) :=
    funext fun t => (pow_two t).symm
  rw [e, h2, pow_two]

theorem kapCfc_one_add_sq (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => 1 + t * t) a = 1 + a * a := by
  have h := cfc_const_add (r := (1 : ℝ)) (f := fun t : ℝ => t * t) (a := a)
    (hf := (by continuity : Continuous (fun t : ℝ => t * t)).continuousOn) (ha := ha)
  rw [kapCfc_sq a ha, map_one] at h
  exact h

theorem kapScalar_inv_left (t : ℝ) : kapR t * (1 + t * t) = 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have e : (1 : ℝ) + t * t = 1 + t ^ 2 := by ring
  unfold kapR
  rw [e]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

theorem kapScalar_inv_right (t : ℝ) : (1 + t * t) * kapR t = 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have e : (1 : ℝ) + t * t = 1 + t ^ 2 := by ring
  unfold kapR
  rw [e]
  exact mul_inv_cancel₀ (ne_of_gt hpos)

/-- Left inverse identity for the resolvent cfc. -/
theorem kapCfcR_mul_left (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcR a * (1 + a * a) = 1 := by
  have hmul := cfc_mul (f := kapR) (g := fun t : ℝ => 1 + t * t) (a := a)
    (hf := kapR_cont.continuousOn)
    (hg := (by continuity : Continuous (fun t : ℝ => 1 + t * t)).continuousOn)
  have hcfc : cfc (fun t : ℝ => kapR t * (1 + t * t)) a = 1 :=
    (cfc_congr (fun t _ => kapScalar_inv_left t)).trans
      (cfc_one (R := ℝ) (a := a) (ha := ha))
  unfold kapCfcR
  rw [← kapCfc_one_add_sq a ha, ← hmul]
  exact hcfc

/-- Right inverse identity for the resolvent cfc. -/
theorem kapCfcR_mul_right (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    (1 + a * a) * kapCfcR a = 1 := by
  have hmul := cfc_mul (f := fun t : ℝ => 1 + t * t) (g := kapR) (a := a)
    (hf := (by continuity : Continuous (fun t : ℝ => 1 + t * t)).continuousOn)
    (hg := kapR_cont.continuousOn)
  have hcfc : cfc (fun t : ℝ => (1 + t * t) * kapR t) a = 1 :=
    (cfc_congr (fun t _ => kapScalar_inv_right t)).trans
      (cfc_one (R := ℝ) (a := a) (ha := ha))
  unfold kapCfcR
  rw [← kapCfc_one_add_sq a ha, ← hmul]
  exact hcfc

theorem kapCfc_mul_self_left (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    a * kapCfcR a = cfc (fun t : ℝ => t * kapR t) a := by
  have h := cfc_mul (f := fun t : ℝ => t) (g := kapR) (a := a)
    (hf := (by continuity : Continuous (fun t : ℝ => t)).continuousOn)
    (hg := kapR_cont.continuousOn)
  have hid : cfc (fun t : ℝ => t) a = a := cfc_id' (R := ℝ) (ha := ha)
  rw [hid] at h
  unfold kapCfcR
  exact h.symm

theorem kapCfc_mul_self_right (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcR a * a = cfc (fun t : ℝ => kapR t * t) a := by
  have h := cfc_mul (f := kapR) (g := fun t : ℝ => t) (a := a)
    (hf := kapR_cont.continuousOn)
    (hg := (by continuity : Continuous (fun t : ℝ => t)).continuousOn)
  have hid : cfc (fun t : ℝ => t) a = a := cfc_id' (R := ℝ) (ha := ha)
  rw [hid] at h
  unfold kapCfcR
  exact h.symm

/-- The Cayley cfc factors through `a * R a`. -/
theorem kapCfcF_eq_left (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcF a = (2 : ℝ) • (a * kapCfcR a) := by
  have hscalar : ∀ t : ℝ, kapF t = 2 * (t * kapR t) := by
    intro t
    unfold kapF kapR
    ring
  have hF : cfc kapF a = cfc (fun t : ℝ => 2 * (t * kapR t)) a :=
    cfc_congr (fun t _ => hscalar t)
  have hsmul : (2 : ℝ) • cfc (fun t : ℝ => t * kapR t) a
      = cfc (fun t : ℝ => 2 * (t * kapR t)) a := by
    have h := cfc_const_mul (r := (2 : ℝ)) (f := fun t : ℝ => t * kapR t) (a := a)
      (hf := kapMul_cont.continuousOn)
    exact h.symm
  have hmul := kapCfc_mul_self_left a ha
  unfold kapCfcF
  rw [hF, ← hsmul, ← hmul]

/-- The Cayley cfc factors through `R a * a`. -/
theorem kapCfcF_eq_right (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) :
    kapCfcF a = (2 : ℝ) • (kapCfcR a * a) := by
  have hscalar : ∀ t : ℝ, kapF t = 2 * (kapR t * t) := by
    intro t
    unfold kapF kapR
    ring
  have hF : cfc kapF a = cfc (fun t : ℝ => 2 * (kapR t * t)) a :=
    cfc_congr (fun t _ => hscalar t)
  have hsmul : (2 : ℝ) • cfc (fun t : ℝ => kapR t * t) a
      = cfc (fun t : ℝ => 2 * (kapR t * t)) a := by
    have h := cfc_const_mul (r := (2 : ℝ)) (f := fun t : ℝ => kapR t * t) (a := a)
      (hf := kapMulR_cont.continuousOn)
    exact h.symm
  have hmul := kapCfc_mul_self_right a ha
  unfold kapCfcF
  rw [hF, ← hsmul, ← hmul]

end KapCayley

section KapCayleyTendsto

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Algebraic identity for the difference of Cayley maps at self-adjoint points. -/
theorem kapCfcF_sub (a b : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) :
    kapCfcF a - kapCfcF b = (2 : ℝ) • (kapCfcR a * (a - b) * kapCfcR b)
      + (1 / 2 : ℝ) • (kapCfcF a * (b - a) * kapCfcF b) := by
  have hFa := kapCfcF_eq_right a ha
  have hFb := kapCfcF_eq_left b hb
  have hRa := kapCfcR_mul_left a ha
  have hRb := kapCfcR_mul_right b hb
  have e1 : kapCfcR a * (a * (1 + b * b)) * kapCfcR b = kapCfcR a * a := by
    rw [mul_assoc (kapCfcR a) _ _, mul_assoc a _ _, hRb, mul_one]
  have e2 : kapCfcR a * ((1 + a * a) * b) * kapCfcR b = b * kapCfcR b := by
    rw [mul_assoc (kapCfcR a) _ _, mul_assoc (1 + a * a) _ _,
      ← mul_assoc (kapCfcR a) _ _, hRa, one_mul]
  have e3 : a * (1 + b * b) - (1 + a * a) * b
      = (a - b) + a * (b - a) * b := by
    noncomm_ring
  have eSub : kapCfcR a * (a * (1 + b * b)) * kapCfcR b
          - kapCfcR a * ((1 + a * a) * b) * kapCfcR b
        = kapCfcR a * (a - b) * kapCfcR b
          + (kapCfcR a * a) * (b - a) * (b * kapCfcR b) := by
    have hbridge : kapCfcR a * (a * (b - a) * b) * kapCfcR b
        = (kapCfcR a * a) * (b - a) * (b * kapCfcR b) := by
      noncomm_ring
    rw [← sub_mul, ← mul_sub, e3, mul_add, add_mul, hbridge]
  have eF : kapCfcF a * (b - a) * kapCfcF b
        = (4 : ℝ) • ((kapCfcR a * a) * (b - a) * (b * kapCfcR b)) := by
    rw [hFa, hFb, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul]
    norm_num
  have eMain : kapCfcF a - kapCfcF b
        = (2 : ℝ) • (kapCfcR a * (a * (1 + b * b)) * kapCfcR b)
        - (2 : ℝ) • (kapCfcR a * ((1 + a * a) * b) * kapCfcR b) := by
    rw [hFa, hFb, ← e1, ← e2]
  rw [eMain, ← smul_sub, eSub, smul_add, eF, smul_smul,
    show (1 / 2 : ℝ) * 4 = 2 by norm_num]

/-- Pointwise norm bound for the Cayley map difference. -/
theorem kapCfcF_bound (a b : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (v : H) :
    ‖(kapCfcF a - kapCfcF b) v‖ ≤ 2 * ‖(a - b) (kapCfcR b v)‖
      + (1 / 2) * ‖(a - b) (kapCfcF b v)‖ := by
  have hsub := kapCfcF_sub a b ha hb
  have hR := kapNorm_cfcR_le a
  have hF := kapNorm_cfcF_le a
  have smul2 : ∀ w : H, ‖(2 : ℝ) • w‖ = 2 * ‖w‖ := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have smulh : ∀ w : H, ‖(1 / 2 : ℝ) • w‖ = (1 / 2) * ‖w‖ := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have b1 : ‖((kapCfcR a * (a - b) * kapCfcR b) v)‖
      ≤ ‖(a - b) (kapCfcR b v)‖ := by
    have e : (kapCfcR a * (a - b) * kapCfcR b) v
        = kapCfcR a ((a - b) (kapCfcR b v)) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [e]
    calc ‖kapCfcR a ((a - b) (kapCfcR b v))‖
        ≤ ‖kapCfcR a‖ * ‖(a - b) (kapCfcR b v)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(a - b) (kapCfcR b v)‖ :=
          mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = ‖(a - b) (kapCfcR b v)‖ := one_mul _
  have b2 : ‖((kapCfcF a * (b - a) * kapCfcF b) v)‖
      ≤ ‖(a - b) (kapCfcF b v)‖ := by
    have e : (kapCfcF a * (b - a) * kapCfcF b) v
        = kapCfcF a ((b - a) (kapCfcF b v)) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    have e2 : (b - a) (kapCfcF b v) = -((a - b) (kapCfcF b v)) := by
      have d : (b - a) (kapCfcF b v) = b (kapCfcF b v) - a (kapCfcF b v) :=
        sub_apply _ _ _
      have d2 : (a - b) (kapCfcF b v) = a (kapCfcF b v) - b (kapCfcF b v) :=
        sub_apply _ _ _
      rw [d, d2, neg_sub]
    have hle : ‖kapCfcF a ((b - a) (kapCfcF b v))‖ ≤ ‖(b - a) (kapCfcF b v)‖ := by
      calc ‖kapCfcF a ((b - a) (kapCfcF b v))‖
          ≤ ‖kapCfcF a‖ * ‖(b - a) (kapCfcF b v)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖(b - a) (kapCfcF b v)‖ :=
            mul_le_mul_of_nonneg_right hF (norm_nonneg _)
        _ = ‖(b - a) (kapCfcF b v)‖ := one_mul _
    have hneg : ‖(b - a) (kapCfcF b v)‖ = ‖(a - b) (kapCfcF b v)‖ := by
      rw [e2, norm_neg]
    rw [e]
    rw [hneg] at hle
    exact hle
  rw [hsub, add_apply, IsSMulApply.smul_apply, IsSMulApply.smul_apply]
  refine (norm_add_le _ _).trans ?_
  rw [smul2, smulh]
  exact add_le_add (mul_le_mul_of_nonneg_left b1 (by norm_num))
    (mul_le_mul_of_nonneg_left b2 (by norm_num))

/-- The Cayley map is SOT-continuous along self-adjoint nets. -/
theorem kapTendsto_cfcF (b : H →L[ℂ] H) (hb : IsSelfAdjoint b) :
    Filter.Tendsto (fun p : H →Lₚₜ[ℂ] H => kapOfBounded (kapCfcF (toBounded p)))
      (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
      (𝓝 (kapOfBounded (kapCfcF b))) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  intro v
  change Filter.Tendsto
    (fun p : H →Lₚₜ[ℂ] H => (kapOfBounded (kapCfcF (toBounded p))) v)
    (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
    (𝓝 ((kapOfBounded (kapCfcF b)) v))
  have hblim : ∀ w : H, Filter.Tendsto
      (fun p : H →Lₚₜ[ℂ] H => ‖(toBounded p - b) w‖)
      (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
      (𝓝 0) := by
    intro w
    have h1 : Filter.Tendsto (fun p : H →Lₚₜ[ℂ] H => p w)
        (𝓝 (kapOfBounded b)) (𝓝 ((kapOfBounded b) w)) :=
      (kapEval_continuous w).tendsto _
    have h2 : Filter.Tendsto (fun p : H →Lₚₜ[ℂ] H => p w)
        (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
        (𝓝 ((kapOfBounded b) w)) :=
      h1.mono_left nhdsWithin_le_nhds
    have e : (fun p : H →Lₚₜ[ℂ] H => ‖(toBounded p - b) w‖)
        = (fun p : H →Lₚₜ[ℂ] H => ‖p w - (kapOfBounded b) w‖) := by
      funext p
      have d1 : (toBounded p - b) w = (toBounded p) w - b w := sub_apply _ _ _
      rw [d1, kapToBounded_apply, kapOfBounded_apply]
    rw [e]
    exact tendsto_iff_norm_sub_tendsto_zero.mp h2
  have hlim : Filter.Tendsto
      (fun p : H →Lₚₜ[ℂ] H => 2 * ‖(toBounded p - b) (kapCfcR b v)‖
        + (1 / 2) * ‖(toBounded p - b) (kapCfcF b v)‖)
      (𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b))
      (𝓝 0) := by
    have h1 := (hblim (kapCfcR b v)).const_mul 2
    have h2 := (hblim (kapCfcF b v)).const_mul (1 / 2)
    rw [mul_zero] at h1 h2
    have h12 := h1.add h2
    rwa [add_zero] at h12
  have hbound : ∀ᶠ p in
      𝓝[{p : H →Lₚₜ[ℂ] H | IsSelfAdjoint (toBounded p)}] (kapOfBounded b),
      ‖(kapOfBounded (kapCfcF (toBounded p))) v - (kapOfBounded (kapCfcF b)) v‖
        ≤ 2 * ‖(toBounded p - b) (kapCfcR b v)‖
          + (1 / 2) * ‖(toBounded p - b) (kapCfcF b v)‖ := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have ha : IsSelfAdjoint (toBounded p) := hp
    have h := kapCfcF_bound (toBounded p) b ha hb v
    have e1 : (kapOfBounded (kapCfcF (toBounded p))) v
          - (kapOfBounded (kapCfcF b)) v
        = (kapCfcF (toBounded p) - kapCfcF b) v := by
      simp only [kapOfBounded_apply, sub_apply]
    rw [e1]
    exact h
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

end KapCayleyTendsto
end Analysis.CStarAlgebra.KaplanskyDensityWanted
