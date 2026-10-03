import sympy.stats.joint_rv
import sympy.stats.policy_trajectory.markov
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Measure.EqRnDeriv_Count
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Bridge between the `ℙ` binder sugar and the policy of a policy-gradient model:
with counting reference measures on the finite state / action spaces, the canonical
conditional density `ℙ[M.traj θ](a[t] = u | s[t] = x)` of the trajectory law equals the policy
probability `π_θ(u | x)` at every reachable state `x` (`Pr(s[t] = x) ≠ 0`).
-/
@[main]
private lemma main
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ} {t : ℕ} {x : S} {u : A}
-- given
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (hP : SinglePSpace (M.traj θ) (a (S := S) (A := A) t, s (S := S) (A := A) t))
  (h : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  ℙ[(M.traj θ)]((a t) = u | (s t) = x) = ENNReal.ofReal (M.pol.prob θ x u) := by
-- proof
  classical
  set π := M.traj θ
  have hAS : (ReferenceMeasure.measure : Measure (A × S)) = Measure.count := by
    show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
    rw [hA, hS, Measure.Count.eq.ProdCountS]
  have hxy : Measurable (a (S := S) (A := A) t, s (S := S) (A := A) t) :=
    (a_meas t).prodMk (s_meas t)
  have hnum : π.prob (a (S := S) (A := A) t, s (S := S) (A := A) t) (u, x) =
      π (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := by
    unfold Measure.prob
    rw [hAS, Measure.EqRnDeriv_Count, Measure.map_apply hxy (measurableSet_singleton _)]
    congr 1
    ext ω
    simp [JointRandomSymbol, and_comm]
  have hden : (π.map (fun ω ↦ ((a (S := S) (A := A) t, s (S := S) (A := A) t) ω).2)).rnDeriv
      ReferenceMeasure.measure x = π (s t ⁻¹' {x}) := by
    rw [hS, Measure.EqRnDeriv_Count]
    exact Measure.map_apply (s_meas t) (measurableSet_singleton _)
  have hxu : π.real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) =
      π.real (s t ⁻¹' {x}) * M.pol.prob θ x u := by
    rw [← P_xu M θ t x u]
    have hset : MeasurableSet (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) :=
      (s_meas t (measurableSet_singleton _)).inter (a_meas t (measurableSet_singleton _))
    rw [← integral_indicator_one hset]
    congr 1
    ext ω
    by_cases h1 : s t ω = x <;> by_cases h2 : a t ω = u <;>
      simp [Set.indicator, h1, h2]
  show π.prob (a (S := S) (A := A) t, s (S := S) (A := A) t) (u, x) /
      (π.map (fun ω ↦ ((a (S := S) (A := A) t, s (S := S) (A := A) t) ω).2)).rnDeriv ReferenceMeasure.measure x = _
  rw [hnum, hden, ← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _),
    hxu, ENNReal.ofReal_mul measureReal_nonneg]
  have h0 : ENNReal.ofReal (π.real (s t ⁻¹' {x})) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact lt_of_le_of_ne measureReal_nonneg (Ne.symm h)
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right h0 ENNReal.ofReal_ne_top


-- created on 2026-09-27
