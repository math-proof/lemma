import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Pn1.eq.P1
import Lemma.Random.RealPreimageSPreimageS_Add.eq.Pn.of.NeRealPreimageS_0
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
On a reachable state (`Pr(s[t] = x) ≠ 0`), `Pr(s[t+1] = y | s[t] = x) = P1 θ x y`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ)
  (x y : S)
  (h₀ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  ((M θ)[|s t ⁻¹' {x}]).real (s (t + 1) ⁻¹' {y}) = M.P1 θ x y := by
-- proof
  rw [Random.RealPreimageSPreimageS_Add.eq.Pn.of.NeRealPreimageS_0 (M := M) θ t 1 x y h₀, Random.Pn1.eq.P1]


-- created on 2026-10-06
