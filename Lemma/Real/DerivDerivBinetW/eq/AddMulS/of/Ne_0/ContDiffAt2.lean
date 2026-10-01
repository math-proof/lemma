import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Lemma.Real.DerivBinetW.eq.MulNegPow.of.Ne_0.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic

open Filter Topology


/--
Binet second derivative (notes eq. 4):
\(w''=-r^{-2}r''+2r^{-3}(r')^2\).
-/
@[main]
private lemma main
  {r : ℝ → ℝ}
  {φ : ℝ}
-- given
  (hr0 : r φ ≠ 0)
  (hr : ContDiffAt ℝ 2 r φ) :
-- imply
  deriv (deriv (binet_w r)) φ =
    -deriv (deriv r) φ / (r φ) ^ 2 + 2 * (deriv r φ) ^ 2 / (r φ) ^ 3 := by
-- proof
  have hr1 : DifferentiableAt ℝ r φ := hr.differentiableAt (by decide)
  have hr' : DifferentiableAt ℝ (deriv r) φ :=
    (hr.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by decide)
  have hr_ne : ∀ᶠ ψ in 𝓝 φ, r ψ ≠ 0 :=
    hr.continuousAt.eventually <|
      eventually_of_mem (isOpen_ne.mem_nhds hr0) fun _ h => h
  have hfin : (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
  have hw' : deriv (binet_w r) =ᶠ[𝓝 φ] fun ψ => -deriv r ψ * ((r ψ) ^ 2)⁻¹ := by
    filter_upwards [hr.eventually hfin, hr_ne] with ψ hψ hrψ
    have := Real.DerivBinetW.eq.MulNegPow.of.Ne_0.DifferentiableAt hrψ
      (hψ.differentiableAt (by decide))
    simpa [div_eq_mul_inv, neg_mul] using this
  have hsq :
      HasDerivAt (fun ψ => r ψ * r ψ) (2 * r φ * deriv r φ) φ :=
    (hr1.hasDerivAt.mul hr1.hasDerivAt).congr_deriv (by ring)
  have hsq' :
      HasDerivAt (fun ψ => (r ψ) ^ 2) (2 * r φ * deriv r φ) φ := by
    refine hsq.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun ψ => pow_two (r ψ)
  have hinv :
      HasDerivAt (fun ψ => ((r ψ) ^ 2)⁻¹) (-2 * deriv r φ / (r φ) ^ 3) φ := by
    have h := hsq'.inv (pow_ne_zero 2 hr0)
    refine h.congr_deriv ?_
    have hr2 : (r φ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
    have hpow : ((r φ) ^ 2) ^ 2 = (r φ) ^ 4 := by ring
    simp only [hpow]
    field_simp [hr0, hr2]
  have hneg : HasDerivAt (fun ψ => -deriv r ψ) (-deriv (deriv r) φ) φ :=
    hr'.hasDerivAt.neg
  have hprod :
      HasDerivAt (fun ψ => -deriv r ψ * ((r ψ) ^ 2)⁻¹)
        (-deriv (deriv r) φ / (r φ) ^ 2 + 2 * (deriv r φ) ^ 2 / (r φ) ^ 3) φ := by
    refine (hneg.mul hinv).congr_deriv ?_
    have hr2 : (r φ) ^ 2 ≠ 0 := pow_ne_zero 2 hr0
    field_simp [hr0, hr2]
  exact (hprod.congr_of_eventuallyEq hw').deriv


-- created on 2026-09-29
