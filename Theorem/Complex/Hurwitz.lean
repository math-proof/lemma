module

public import Mathlib
public import Theorem.Analysis.Complex.Hurwitz.Part2

public section

open Filter Metric Set
open scoped Topology


/--
[TendstoLocallyUniformlyOn.eqOn_zero_or_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Hurwitz.lean)
-/
public theorem eqOn_zero_or_ne_zero_eq
-- given
  {α : Type*} {F : α → ℂ → ℂ} {f : ℂ → ℂ} {φ : Filter α} {U : Set ℂ}
  [φ.NeBot]
  (hf : TendstoLocallyUniformlyOn F f φ U)
  (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
  (hU : IsOpen U) (hUc : IsPreconnected U)
  (hF_ne : ∀ᶠ n in φ, ∀ z ∈ U, F n z ≠ 0) :
-- imply
  Set.EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 :=
-- proof
  hf.eqOn_zero_or_ne_zero hF hU hUc hF_ne

/--
[TendstoLocallyUniformlyOn.ne_zero_of_exists_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Hurwitz.lean)
-/
public theorem ne_zero_of_exists_ne_zero_eq
-- given
  {α : Type*} {F : α → ℂ → ℂ} {f : ℂ → ℂ} {φ : Filter α} {U : Set ℂ}
  [φ.NeBot]
  (hf : TendstoLocallyUniformlyOn F f φ U)
  (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
  (hU : IsOpen U) (hUc : IsPreconnected U)
  (hF_ne : ∀ᶠ n in φ, ∀ z ∈ U, F n z ≠ 0)
  (hf_ne : ∃ z ∈ U, f z ≠ 0) :
-- imply
  ∀ z ∈ U, f z ≠ 0 :=
-- proof
  hf.ne_zero_of_exists_ne_zero hF hU hUc hF_ne hf_ne


-- created on 2026-10-09
-- updated on 2026-10-26
