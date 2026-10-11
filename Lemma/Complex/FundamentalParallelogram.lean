import Mathlib
import sympy.Basic
import sympy.functions.special.elliptic.FundamentalParallelogram


/--
[FundamentalParallelogram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/FundamentalParallelogram.lean)
-/
@[path]
private lemma fundamental_parallelogram_zero_eq
-- given
  (L : PeriodPair) :
-- imply
  L.fundamentalParallelogram 0 = ZSpan.fundamentalDomain L.basis := by
-- proof
  apply PeriodPair.fundamentalParallelogram_zero L

/--
[FundamentalParallelogram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/FundamentalParallelogram.lean)
-/
@[path]
private lemma basis_repr_omega_eq
-- given
  (L : PeriodPair)
  (t₁ t₂ : ℝ)
  (i : Fin 2) :
-- imply
  L.basis.repr (t₁ • L.ω₁ + t₂ • L.ω₂) i = ![t₁, t₂] i := by
-- proof
  apply PeriodPair.basis_repr_omega L t₁ t₂ i

/--
[FundamentalParallelogram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/FundamentalParallelogram.lean)
-/
@[path]
private lemma mem_fundamental_parallelogram_iff_iff
-- given
  (L : PeriodPair)
  (α z : ℂ) :
-- imply
  z ∈ L.fundamentalParallelogram α ↔
    ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
      z = α + t₁ • L.ω₁ + t₂ • L.ω₂ := by
-- proof
  apply PeriodPair.mem_fundamentalParallelogram_iff L


-- created on 2026-10-11
