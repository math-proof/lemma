/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Def.Analysis.Complex.HartogsExtension


namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsextBarEvalCLM_apply
    {n : ℕ} (i : Fin n) (L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) :
    hartogsextBarEvalCLM i L =
      (2 : ℂ)⁻¹ *
        (L (EuclideanSpace.single i 1) +
          Complex.I * L (EuclideanSpace.single i Complex.I)) := by
  simp only [hartogsextBarEvalCLM, ContinuousLinearMap.comp_add, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.mul_apply']
  exact (mul_add _ _ _).symm

theorem hartogsextBarPartial_eq_barEval
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial i f x = hartogsextBarEvalCLM i (fderiv ℝ f x) := by
  rw [hartogsextBarPartial, hartogsextBarEvalCLM_apply]

theorem hartogsext_barPartial_mul
    {n : ℕ} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    hartogsextBarPartial i (fun y ↦ f y * g y) x =
      hartogsextBarPartial i f x * g x + f x * hartogsextBarPartial i g x := by
  rw [hartogsextBarPartial, fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hartogsextBarPartial, hartogsextBarPartial]
  ring

theorem hartogsext_barPartial_add
    {n : ℕ} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    hartogsextBarPartial i (fun y ↦ f y + g y) x =
      hartogsextBarPartial i f x + hartogsextBarPartial i g x := by
  rw [hartogsextBarPartial, fderiv_fun_add hf hg]
  simp only [add_apply]
  rw [hartogsextBarPartial, hartogsextBarPartial]
  ring

theorem hartogsext_barPartial_one_sub
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hartogsextBarPartial i (fun y ↦ 1 - f y) x =
      -hartogsextBarPartial i f x := by
  rw [hartogsextBarPartial, fderiv_const_sub]
  simp only [neg_apply]
  rw [hartogsextBarPartial]
  ring

theorem hartogsext_barPartial_comm
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial i (hartogsextBarPartial j f) x =
      hartogsextBarPartial j (hartogsextBarPartial i f) x := by
  let Ci := hartogsextBarEvalCLM i
  let Cj := hartogsextBarEvalCLM j
  let D2 := fderiv ℝ (fderiv ℝ f) x
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hfj : hartogsextBarPartial j f = Cj ∘ fderiv ℝ f := by
    funext y
    exact hartogsextBarPartial_eq_barEval j f y
  have hfi : hartogsextBarPartial i f = Ci ∘ fderiv ℝ f := by
    funext y
    exact hartogsextBarPartial_eq_barEval i f y
  have hj : HasFDerivAt (hartogsextBarPartial j f) (Cj.comp D2) x := by
    rw [hfj]
    exact (Cj.hasFDerivAt (x := fderiv ℝ f x)).comp x hD.hasFDerivAt
  have hi : HasFDerivAt (hartogsextBarPartial i f) (Ci.comp D2) x := by
    rw [hfi]
    exact (Ci.hasFDerivAt (x := fderiv ℝ f x)).comp x hD.hasFDerivAt
  rw [hartogsextBarPartial_eq_barEval, hartogsextBarPartial_eq_barEval,
    hj.fderiv, hi.fderiv]
  dsimp only [Ci, Cj]
  simp only [hartogsextBarEvalCLM_apply, ContinuousLinearMap.comp_apply]
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num)
  rw [hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
    hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j Complex.I),
    hsymm (EuclideanSpace.single i Complex.I) (EuclideanSpace.single j 1),
    hsymm (EuclideanSpace.single i Complex.I) (EuclideanSpace.single j Complex.I)]
  ring

theorem hartogsext_contDiff_barPartial
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (hartogsextBarPartial i f) := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  unfold hartogsextBarPartial
  exact contDiff_const.mul
    ((hDf.clm_apply contDiff_const).add
      (contDiff_const.mul (hDf.clm_apply contDiff_const)))

theorem hartogsext_hasCompactSupport_barPartial
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (hartogsextBarPartial i f) := by
  have h1 := hf.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hI := hf.fderiv_apply ℝ (EuclideanSpace.single i Complex.I)
  have hsum : HasCompactSupport
      ((fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) +
        (fun _ : EuclideanSpace ℂ (Fin n) ↦ Complex.I) *
          fun x ↦ fderiv ℝ f x (EuclideanSpace.single i Complex.I)) :=
    HasCompactSupport.add h1 (HasCompactSupport.mul_left hI)
  have hscaled := HasCompactSupport.mul_left hsum
    (f := fun _ : EuclideanSpace ℂ (Fin n) ↦ (2 : ℂ)⁻¹)
  change HasCompactSupport
    (fun x ↦ (2 : ℂ)⁻¹ *
      (fderiv ℝ f x (EuclideanSpace.single i 1) +
        Complex.I * fderiv ℝ f x (EuclideanSpace.single i Complex.I)))
  convert hscaled using 1

theorem hartogsext_tsupport_barPartial_subset
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ} (i : Fin n) :
    tsupport (hartogsextBarPartial i f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxt
  rw [Function.mem_support] at hx
  have hfd : fderiv ℝ f x = 0 := fderiv_of_notMem_tsupport ℝ hxt
  exact hx (by simp [hartogsextBarPartial, hfd])

theorem hartogsext_barPartial_eq_zero_of_notMem_tsupport
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ∉ tsupport f) (i : Fin n) :
    hartogsextBarPartial i f x = 0 := by
  rw [hartogsextBarPartial, fderiv_of_notMem_tsupport ℝ hx]
  simp

theorem hartogsext_barPartial_eq_zero_of_differentiableAt
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℂ f x) (i : Fin n) :
    hartogsextBarPartial i f x = 0 := by
  rw [hartogsextBarPartial, hf.fderiv_restrictScalars (𝕜 := ℝ)]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have hsingle : EuclideanSpace.single i Complex.I =
      Complex.I • EuclideanSpace.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hsingle, map_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  simp

theorem hartogsext_tsupport_barPartial_subset_compl
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {V : Set (EuclideanSpace ℂ (Fin n))} (hV : IsOpen V)
    (hf : Set.EqOn f (fun _ ↦ 1) V) (i : Fin n) :
    tsupport (hartogsextBarPartial i f) ⊆ Vᶜ := by
  apply closure_minimal _ hV.isClosed_compl
  intro x hx
  rw [mem_compl_iff]
  intro hxV
  have hxV' : x ∈ V := by simpa using hxV
  have hconst : Filter.EventuallyEq (nhds x) f (fun _ ↦ 1) := by
    filter_upwards [hV.mem_nhds hxV'] with y hy
    exact hf hy
  have hfd : fderiv ℝ f x = 0 :=
    (hasFDerivAt_zero_of_eventually_const (1 : ℂ) hconst).fderiv
  rw [Function.mem_support] at hx
  exact hx (by simp [hartogsextBarPartial, hfd])

end Complex.HartogsWanted
