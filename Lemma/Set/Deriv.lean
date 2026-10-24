import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma nested_eq
  (f : ℝ × ℝ → ℂ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ U)
  (hf : ContDiffOn ℝ 2 f U)
  (a b : ℝ × ℝ) :
  deriv (fun s : ℝ => deriv (fun t : ℝ => f (s • a + t • b)) 0) 0 = fderiv ℝ (fderiv ℝ f) (0, 0) a b := by
  have hdiff : ∀ p ∈ U, DifferentiableAt ℝ f p := fun p hp =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hf0 : ContDiffAt ℝ 2 f (0, 0) := hf.contDiffAt (hU.mem_nhds h0)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (0, 0) :=
    (hf0.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : ∀ᶠ s in nhds (0 : ℝ), deriv (fun t : ℝ => f (s • a + t • b)) 0 = fderiv ℝ f (s • a) b := by
    have hc : Continuous fun s : ℝ => s • a := continuous_id.smul continuous_const
    have hop : IsOpen ((fun s : ℝ => s • a) ⁻¹' U) := hc.isOpen_preimage U hU
    have hmem : (0 : ℝ) ∈ (fun s : ℝ => s • a) ⁻¹' U := by
      simp at h0 ⊢
      refine h0
    filter_upwards [hop.mem_nhds hmem] with s hs
    have hcurve : HasDerivAt (fun t : ℝ => s • a + t • b) b 0 := by
      have this := ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add (s • a)
      simp at this
      refine this
    have hcomp := (hdiff _ hs).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
    refine hcomp.deriv
  rw [Filter.EventuallyEq.deriv_eq hnear]
  have hcurve : HasDerivAt (fun s : ℝ => s • a) a 0 := by
    have this := (hasDerivAt_id (0 : ℝ)).smul_const a
    simp at this
    refine this
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • a)) (fderiv ℝ (fderiv ℝ f) (0, 0) a) 0 :=
    hfd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (s • a) b) (fderiv ℝ (fderiv ℝ f) (0, 0) a b) 0 := by
    have this := h1.clm_apply (hasDerivAt_const (0 : ℝ) b)
    simp at this
    refine this
  refine h2.deriv
/--
[deriv_deriv_comm_of_contDiffOn](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_deriv_deriv_comm_of_contDiffOn.lean)
-/
@[path]
private lemma main
  (F : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ U)
  (hF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) U) :
  -- imply
  deriv (fun s : ℝ => deriv (fun t : ℝ => F s t) 0) 0 =
    deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0 := by
  -- proof
  set f : ℝ × ℝ → ℂ := fun p => F p.1 p.2 with hf
  have hsymm : IsSymmSndFDerivAt ℝ f (0, 0) :=
    (hF.contDiffAt (hU.mem_nhds h0)).isSymmSndFDerivAt (by simp)
  have e1 : deriv (fun s : ℝ => deriv (fun t : ℝ => F s t) 0) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ => f (s • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)))) 0) 0 := by
    congr 1
    funext s
    congr 1
    funext t
    simp [hf]
  have e2 : deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0 =
      deriv (fun t : ℝ => deriv (fun s : ℝ => f (t • ((0 : ℝ), (1 : ℝ)) + s • ((1 : ℝ), (0 : ℝ)))) 0) 0 := by
    congr 1
    funext t
    congr 1
    funext s
    simp [hf]
  rw [e1, e2, nested_eq f U hU h0 hF, nested_eq f U hU h0 hF]
  refine hsymm _ _


-- created on 2026-10-20
