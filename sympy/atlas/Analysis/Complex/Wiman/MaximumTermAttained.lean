/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean -/

import sympy.atlas.Analysis.Complex.Wiman.RadialMajorant
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Order.Compact

namespace Complex

noncomputable section

open Filter Set

/-- The radial Taylor terms are bounded above by their summable majorant. -/
theorem bddAbove_range_wimanTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℝ) :
    BddAbove (range (wimanTerm f r)) := by
  refine ⟨wimanMajorant f r, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact wimanTerm_le_wimanMajorant f hf r n

/-- Every Taylor term is bounded by the supremal maximum term. -/
theorem wimanTerm_le_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (r : ℝ) (n : ℕ) :
    wimanTerm f r n ≤ wimanMaximumTerm f r := by
  rw [wimanMaximumTerm]
  exact le_csSup (bddAbove_range_wimanTerm f hf r) ⟨n, rfl⟩

/-- The maximum term is below a bound exactly when every Taylor term is. -/
theorem wimanMaximumTerm_le_iff
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (r a : ℝ) :
    wimanMaximumTerm f r ≤ a ↔ ∀ n : ℕ, wimanTerm f r n ≤ a := by
  constructor
  · intro h n
    exact (wimanTerm_le_wimanMaximumTerm f hf r n).trans h
  · intro h
    rw [wimanMaximumTerm]
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    exact h n

/-- A summable nonnegative Taylor-term sequence realizes its supremum. -/
theorem exists_wimanTerm_eq_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (r : ℝ) :
    ∃ n : ℕ, wimanTerm f r n = wimanMaximumTerm f r := by
  by_cases hzero : ∀ n : ℕ, wimanTerm f r n = 0
  · refine ⟨0, (wimanTerm_le_wimanMaximumTerm f hf r 0).antisymm ?_⟩
    apply (wimanMaximumTerm_le_iff f hf r (wimanTerm f r 0)).2
    intro n
    rw [hzero n, hzero 0]
  · push Not at hzero
    obtain ⟨n₀, hn₀⟩ := hzero
    have hn₀pos : 0 < wimanTerm f r n₀ :=
      lt_of_le_of_ne (wimanTerm_nonneg f r n₀) (Ne.symm hn₀)
    have htail_cocompact :
        ∀ᶠ n in cocompact ℕ, wimanTerm f r n ≤ wimanTerm f r n₀ := by
      rw [Filter.cocompact_eq_cofinite]
      exact ((summable_wimanTerm f hf r).tendsto_cofinite_zero.eventually_lt_const
        hn₀pos).mono fun _ hn ↦ hn.le
    have hcontinuous : Continuous (wimanTerm f r) :=
      continuous_of_discreteTopology
    obtain ⟨n, hn⟩ := hcontinuous.exists_forall_ge' n₀ htail_cocompact
    refine ⟨n, (wimanTerm_le_wimanMaximumTerm f hf r n).antisymm ?_⟩
    exact (wimanMaximumTerm_le_iff f hf r (wimanTerm f r n)).2 hn

end
