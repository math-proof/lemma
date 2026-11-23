module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Analysis.Complex.Wiman.MaximumTermAttained

public section

open Filter Set
open Complex


/--
[bddAbove_range_wimanTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
public theorem bddAbove_range_wimanTerm
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  BddAbove (range (wimanTerm f r)) := by
-- proof
  refine ⟨wimanMajorant f r, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact wimanTerm_le_wimanMajorant (f := f) (r := r) (n := n) hf


/--
[wimanTerm_le_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
public theorem wimanTerm_le_wimanMaximumTerm
  {f : ℂ → ℂ}
  {r : ℝ}
  {n : ℕ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTerm f r n ≤ wimanMaximumTerm f r := by
-- proof
  rw [wimanMaximumTerm]
  exact le_csSup (bddAbove_range_wimanTerm (f := f) (r := r) hf) ⟨n, rfl⟩


/--
[wimanMaximumTerm_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
public theorem wimanMaximumTerm_le_iff
  {f : ℂ → ℂ}
  {r a : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanMaximumTerm f r ≤ a ↔ ∀ n : ℕ, wimanTerm f r n ≤ a := by
-- proof
  constructor
  · intro h n
    exact (wimanTerm_le_wimanMaximumTerm (f := f) (r := r) (n := n) hf).trans h
  · intro h
    rw [wimanMaximumTerm]
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    exact h n


/--
[exists_wimanTerm_eq_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
public theorem exists_wimanTerm_eq_wimanMaximumTerm
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ∃ n : ℕ, wimanTerm f r n = wimanMaximumTerm f r := by
-- proof
  by_cases hzero : ∀ n : ℕ, wimanTerm f r n = 0
  · refine ⟨0, (wimanTerm_le_wimanMaximumTerm (f := f) (r := r) (n := 0) hf).antisymm ?_⟩
    apply (wimanMaximumTerm_le_iff (f := f) (r := r) (a := wimanTerm f r 0) hf).2
    intro n
    rw [hzero n, hzero 0]
  · push Not at hzero
    obtain ⟨n₀, hn₀⟩ := hzero
    have hn₀pos : 0 < wimanTerm f r n₀ :=
      lt_of_le_of_ne (wimanTerm_nonneg (f := f) (r := r) (n := n₀)) (Ne.symm hn₀)
    have htail_cocompact :
      ∀ᶠ n in cocompact ℕ, wimanTerm f r n ≤ wimanTerm f r n₀ := by
      rw [Filter.cocompact_eq_cofinite]
      exact ((summable_wimanTerm (f := f) (r := r) hf).tendsto_cofinite_zero.eventually_lt_const
        hn₀pos).mono fun _ hn ↦ hn.le
    have hcontinuous : Continuous (wimanTerm f r) :=
      continuous_of_discreteTopology
    obtain ⟨n, hn⟩ := hcontinuous.exists_forall_ge' n₀ htail_cocompact
    refine ⟨n, (wimanTerm_le_wimanMaximumTerm (f := f) (r := r) (n := n) hf).antisymm ?_⟩
    exact (wimanMaximumTerm_le_iff (f := f) (r := r) (a := wimanTerm f r n) hf).2 hn



-- created on 2026-10-20
-- updated on 2026-11-23
