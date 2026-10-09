import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Lemma.Real.StronglyMeasurable_Eq22
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`∫ z, 1{z.a = u} * g z ∂(stageK θ x) = π_θ(u | x) * ∫ ρ, g (ρ, x, u) ∂(reward (x, u))`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq A]
  {M : Model Θ S A}
  {g : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (x : S)
  (u : A) :
-- imply
  ∫ z, (if z.2.2 = u then (1:ℝ) else 0) * g z ∂(M.stageK θ x) =
    M.pol.prob θ x u * ∫ ρ, g (ρ, x, u) ∂(M.env.reward (x, u)) := by
-- proof
  rw [Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable (M := M) ((Real.StronglyMeasurable_Eq22 u).mul hg) (f := fun z => (if z.2.2 = u then (1:ℝ) else 0) * g z)
    (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × S × A => z.2.2 = u)) hC) θ]
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [hb]) (by simp)]
  simp [smul_eq_mul]


-- created on 2026-10-07
