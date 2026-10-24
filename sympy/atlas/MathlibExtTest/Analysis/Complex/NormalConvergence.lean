/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/NormalConvergence.lean -/


import Lemma.Real.Complex.NormalConvergence

/-!
# Tests for normal convergence APIs

Exercises the normal-convergence API on a concrete nonzero complex one-term
series, including absolute, uniform, and locally uniform convergence and
termwise differentiation.
-/


open Complex MeasureTheory Topology Set Filter

namespace N329Test

/-- Concrete nonzero complex one-term series used for testing. -/
def complexOneTermSeries : Nat → Complex → Complex :=
  fun n _ => if n = 0 then 1 else 0

/-- Direct example invoking `summable_toReal_supNormOn`. -/
example : Summable (fun n => (supNormOn (complexOneTermSeries n) Set.univ).toReal) :=
  complexOneTermSeries_convergesNormallyOn.summable_toReal_supNormOn

/-- Normal convergence gives pointwise absolute convergence. -/
example (z : Complex) : Summable (fun n => ‖complexOneTermSeries n z‖) :=
  complexOneTermSeries_convergesNormallyOn.summable_norm (Set.mem_univ z)

/-- Local normal convergence gives pointwise absolute convergence. -/
example (z : Complex) : Summable (fun n => ‖complexOneTermSeries n z‖) :=
  complexOneTermSeries_convergesLocallyNormallyOn.summable_norm (Set.mem_univ z)

/-- Direct example invoking `tendstoUniformlyOn_tsum_nat`. -/
example :
    TendstoUniformlyOn
      (fun k z => ∑ n ∈ Finset.range k, complexOneTermSeries n z)
      (fun z => ∑' n, complexOneTermSeries n z) Filter.atTop Set.univ :=
  complexOneTermSeries_convergesNormallyOn.tendstoUniformlyOn_tsum_nat

/-- Direct example invoking `tendstoLocallyUniformlyOn_tsum_nat`. -/
example :
    TendstoLocallyUniformlyOn
      (fun k z => ∑ n ∈ Finset.range k, complexOneTermSeries n z)
      (fun z => ∑' n, complexOneTermSeries n z) Filter.atTop Set.univ :=
  complexOneTermSeries_convergesLocallyNormallyOn.tendstoLocallyUniformlyOn_tsum_nat

/-- Exercise the `deriv` theorem on the concrete series. -/
example :
    ConvergesLocallyNormallyOn
      (fun n w => deriv (complexOneTermSeries n) w) Set.univ :=
  complexOneTermSeries_convergesLocallyNormallyOn.deriv isOpen_univ
    complexOneTermSeries_differentiableOn

/-- Exercise the `hasDerivAt_tsum` theorem on the concrete series. -/
example (z : Complex) :
    HasDerivAt (fun w => ∑' n, complexOneTermSeries n w)
      (∑' n, deriv (complexOneTermSeries n) z) z :=
  complexOneTermSeries_convergesLocallyNormallyOn.hasDerivAt_tsum isOpen_univ
    complexOneTermSeries_differentiableOn (Set.mem_univ z)

/-- The concrete series sums to one everywhere. -/
example (z : Complex) : (∑' n, complexOneTermSeries n z) = 1 := by
  simp [complexOneTermSeries, tsum_eq_single 0]

/-- The derivative theorem remains polymorphic in the complex normed codomain. -/
example :
    ConvergesLocallyNormallyOn
      (fun n z => deriv ((0 : Nat → Complex → Complex × Complex) n) z) Set.univ := by
  have hzero : ConvergesLocallyNormallyOn
      (0 : Nat → Complex → Complex × Complex) Set.univ :=
    convergesLocallyNormallyOn_zero Set.univ
  apply hzero.deriv isOpen_univ
  intro n
  change DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ × ℂ)) Set.univ
  exact differentiableOn_const _

end N329Test
