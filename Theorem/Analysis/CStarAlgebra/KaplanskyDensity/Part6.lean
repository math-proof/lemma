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
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part6
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapL2Prod

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem kapInl_ofLp (v : H) : (kapInl v).ofLp = (v, 0) := rfl

omit [CompleteSpace H] in
theorem kapInr_ofLp (v : H) : (kapInr v).ofLp = (0, v) := rfl

omit [CompleteSpace H] in
theorem kapFst_ofLp (w : WithLp 2 (H × H)) : kapFst w = (w.ofLp).1 := by
  have h1 : kapFst w = w.fst := WithLp.fstL_apply 2 ℂ H H w
  have h2 : w.fst = (w.ofLp).1 := (WithLp.ofLp_fst w).symm
  exact h1.trans h2

omit [CompleteSpace H] in
theorem kapSnd_ofLp (w : WithLp 2 (H × H)) : kapSnd w = (w.ofLp).2 := by
  have h1 : kapSnd w = w.snd := WithLp.sndL_apply 2 ℂ H H w
  have h2 : w.snd = (w.ofLp).2 := (WithLp.ofLp_snd w).symm
  exact h1.trans h2

omit [CompleteSpace H] in
theorem kapInl_apply' (v : H) : kapInl v = WithLp.toLp 2 (v, (0 : H)) := by
  conv_lhs => rw [← WithLp.toLp_ofLp 2 (kapInl v), kapInl_ofLp]

omit [CompleteSpace H] in
theorem kapInr_apply' (v : H) : kapInr v = WithLp.toLp 2 ((0 : H), v) := by
  conv_lhs => rw [← WithLp.toLp_ofLp 2 (kapInr v), kapInr_ofLp]

omit [CompleteSpace H] in
theorem kapFst_inl : kapFst ∘L kapInl = ContinuousLinearMap.id ℂ H := by
  ext v
  change kapFst (kapInl v) = v
  rw [kapFst_ofLp, kapInl_ofLp]

omit [CompleteSpace H] in
theorem kapSnd_inr : kapSnd ∘L kapInr = ContinuousLinearMap.id ℂ H := by
  ext v
  change kapSnd (kapInr v) = v
  rw [kapSnd_ofLp, kapInr_ofLp]

omit [CompleteSpace H] in
theorem kapFst_inr : kapFst ∘L kapInr = (0 : H →L[ℂ] H) := by
  ext v
  change kapFst (kapInr v) = 0
  rw [kapFst_ofLp, kapInr_ofLp]

omit [CompleteSpace H] in
theorem kapSnd_inl : kapSnd ∘L kapInl = (0 : H →L[ℂ] H) := by
  ext v
  change kapSnd (kapInl v) = 0
  rw [kapSnd_ofLp, kapInl_ofLp]

omit [CompleteSpace H] in
theorem kapProj_sum : kapInl ∘L kapFst + kapInr ∘L kapSnd
    = ContinuousLinearMap.id ℂ (WithLp 2 (H × H)) := by
  ext w
  change kapInl (kapFst w) + kapInr (kapSnd w) = w
  rw [kapInl_apply', kapInr_apply', kapFst_ofLp, kapSnd_ofLp, ← WithLp.toLp_add,
    Prod.mk_add_mk, add_zero, zero_add]

theorem kapAdjoint_inl :
    ContinuousLinearMap.adjoint (kapInl : H →L[ℂ] WithLp 2 (H × H)) = kapFst := by
  have h : kapFst
      = ContinuousLinearMap.adjoint (kapInl : H →L[ℂ] WithLp 2 (H × H)) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [WithLp.prod_inner_apply, kapInl_ofLp, kapFst_ofLp]
    have e1 : ((y, (0 : H)).1) = y := rfl
    have e2 : ((y, (0 : H)).2) = 0 := rfl
    rw [e1, e2, inner_zero_right, add_zero]
  exact h.symm

theorem kapAdjoint_inr :
    ContinuousLinearMap.adjoint (kapInr : H →L[ℂ] WithLp 2 (H × H)) = kapSnd := by
  have h : kapSnd
      = ContinuousLinearMap.adjoint (kapInr : H →L[ℂ] WithLp 2 (H × H)) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [WithLp.prod_inner_apply, kapInr_ofLp, kapSnd_ofLp]
    have e1 : (((0 : H), y).1) = 0 := rfl
    have e2 : (((0 : H), y).2) = y := rfl
    rw [e1, e2, inner_zero_right, zero_add]
  exact h.symm

theorem kapAdjoint_fst :
    ContinuousLinearMap.adjoint (kapFst : WithLp 2 (H × H) →L[ℂ] H) = kapInl := by
  have h : kapInl
      = ContinuousLinearMap.adjoint (kapFst : WithLp 2 (H × H) →L[ℂ] H) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x v
    rw [WithLp.prod_inner_apply, kapInl_ofLp, kapFst_ofLp]
    have e1 : ((x, (0 : H)).1) = x := rfl
    have e2 : ((x, (0 : H)).2) = 0 := rfl
    rw [e1, e2, inner_zero_left, add_zero]
  exact h.symm

theorem kapAdjoint_snd :
    ContinuousLinearMap.adjoint (kapSnd : WithLp 2 (H × H) →L[ℂ] H) = kapInr := by
  have h : kapInr
      = ContinuousLinearMap.adjoint (kapSnd : WithLp 2 (H × H) →L[ℂ] H) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x v
    rw [WithLp.prod_inner_apply, kapInr_ofLp, kapSnd_ofLp]
    have e1 : (((0 : H), x).1) = 0 := rfl
    have e2 : (((0 : H), x).2) = x := rfl
    rw [e1, e2, inner_zero_left, zero_add]
  exact h.symm

omit [CompleteSpace H] in
theorem kapNorm_sq (v : WithLp 2 (H × H)) :
    ‖v‖ ^ 2 = ‖kapFst v‖ ^ 2 + ‖kapSnd v‖ ^ 2 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  have e1 : kapFst v = v.fst := WithLp.fstL_apply 2 ℂ H H v
  have e2 : kapSnd v = v.snd := WithLp.sndL_apply 2 ℂ H H v
  rw [e1, e2]
  exact h

omit [CompleteSpace H] in
theorem kapNorm_fst_le : ‖(kapFst : WithLp 2 (H × H) →L[ℂ] H)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
  rw [one_mul]
  have h := WithLp.prod_norm_sq_eq_of_L2 w
  have e1 : kapFst w = w.fst := WithLp.fstL_apply 2 ℂ H H w
  rw [e1]
  have h2 : ‖w.fst‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖w.snd‖ ^ 2 := sq_nonneg _
    linarith
  have h3 : |‖w.fst‖| ≤ ‖w‖ := abs_le_of_sq_le_sq h2 (norm_nonneg _)
  rwa [abs_of_nonneg (norm_nonneg _)] at h3

omit [CompleteSpace H] in
theorem kapNorm_inr_le : ‖(kapInr : H →L[ℂ] WithLp 2 (H × H))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul, kapInr_apply', WithLp.norm_toLp_snd]

omit [CompleteSpace H] in
theorem kapFst_kapInl_apply (v : H) : kapFst (kapInl v) = v := by
  have h : (kapFst ∘L kapInl) v = (ContinuousLinearMap.id ℂ H) v :=
    congrArg (fun F => F v) kapFst_inl
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

omit [CompleteSpace H] in
theorem kapFst_kapInr_apply (v : H) : kapFst (kapInr v) = 0 := by
  have h : (kapFst ∘L kapInr) v = (0 : H →L[ℂ] H) v :=
    congrArg (fun F => F v) kapFst_inr
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h

omit [CompleteSpace H] in
theorem kapSnd_kapInl_apply (v : H) : kapSnd (kapInl v) = 0 := by
  have h : (kapSnd ∘L kapInl) v = (0 : H →L[ℂ] H) v :=
    congrArg (fun F => F v) kapSnd_inl
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h

omit [CompleteSpace H] in
theorem kapSnd_kapInr_apply (v : H) : kapSnd (kapInr v) = v := by
  have h : (kapSnd ∘L kapInr) v = (ContinuousLinearMap.id ℂ H) v :=
    congrArg (fun F => F v) kapSnd_inr
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

omit [CompleteSpace H] in
theorem kapProj_apply (w : WithLp 2 (H × H)) :
    kapInl (kapFst w) + kapInr (kapSnd w) = w := by
  have h := DFunLike.congr_fun kapProj_sum w
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

omit [CompleteSpace H] in
/-- A corner of a product expands over the middle projection sum. -/
theorem kapCorner_mul_eq
    (T U : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (A : WithLp 2 (H × H) →L[ℂ] H) (B : H →L[ℂ] WithLp 2 (H × H)) :
    A ∘L (T * U) ∘L B
      = (A ∘L T ∘L kapInl) * (kapFst ∘L U ∘L B)
        + (A ∘L T ∘L kapInr) * (kapSnd ∘L U ∘L B) := by
  ext v
  simp only [add_apply, mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
  have hproj := kapProj_apply (U (B v))
  conv_lhs => rw [← hproj]
  simp only [map_add]

/-- The `(1,1)` corner of `star T` is the star of the `(1,1)` corner of `T`. -/
theorem kapCorner_star_11 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapFst ∘L star T ∘L kapInl = star (kapFst ∘L T ∘L kapInl) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inl, kapAdjoint_fst]

/-- The `(1,2)` corner of `star T` is the star of the `(2,1)` corner of `T`. -/
theorem kapCorner_star_12 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapFst ∘L star T ∘L kapInr = star (kapSnd ∘L T ∘L kapInl) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inl, kapAdjoint_snd]

/-- The `(2,1)` corner of `star T` is the star of the `(1,2)` corner of `T`. -/
theorem kapCorner_star_21 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapSnd ∘L star T ∘L kapInl = star (kapFst ∘L T ∘L kapInr) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inr, kapAdjoint_fst]

/-- The `(2,2)` corner of `star T` is the star of the `(2,2)` corner of `T`. -/
theorem kapCorner_star_22 (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :
    kapSnd ∘L star T ∘L kapInr = star (kapSnd ∘L T ∘L kapInr) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inr, kapAdjoint_snd]

omit [CompleteSpace H] in
/-- A corner of a sum is the sum of the corners. -/
theorem kapCorner_add_eq
    (S T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (A : WithLp 2 (H × H) →L[ℂ] H) (B : H →L[ℂ] WithLp 2 (H × H)) :
    A ∘L (S + T) ∘L B = A ∘L S ∘L B + A ∘L T ∘L B := by
  ext v
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]

omit [CompleteSpace H] in
/-- A corner of zero is zero. -/
theorem kapCorner_zero_eq
    (A : WithLp 2 (H × H) →L[ℂ] H) (B : H →L[ℂ] WithLp 2 (H × H)) :
    A ∘L (0 : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) ∘L B = 0 := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, map_zero, zero_apply]

omit [CompleteSpace H] in
/-- The `(1,1)` corner of a scalar is the scalar. -/
theorem kapCorner_alg_11 (c : ℂ) :
    kapFst ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInl
      = algebraMap ℂ (H →L[ℂ] H) c := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapFst_kapInl_apply]

omit [CompleteSpace H] in
/-- The `(1,2)` corner of a scalar is zero. -/
theorem kapCorner_alg_12 (c : ℂ) :
    kapFst ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInr
      = 0 := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapFst_kapInr_apply, smul_zero,
    zero_apply]

omit [CompleteSpace H] in
/-- The `(2,1)` corner of a scalar is zero. -/
theorem kapCorner_alg_21 (c : ℂ) :
    kapSnd ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInl
      = 0 := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapSnd_kapInl_apply, smul_zero,
    zero_apply]

omit [CompleteSpace H] in
/-- The `(2,2)` corner of a scalar is the scalar. -/
theorem kapCorner_alg_22 (c : ℂ) :
    kapSnd ∘L algebraMap ℂ (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) c ∘L kapInr
      = algebraMap ℂ (H →L[ℂ] H) c := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul, kapSnd_kapInr_apply]

end KapL2Prod
end Analysis.CStarAlgebra.KaplanskyDensityWanted
