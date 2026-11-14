import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogram


namespace PeriodPair

/--
[FundamentalParallelogram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/FundamentalParallelogram.lean)
-/
@[path]
private lemma fundamentalParallelogram_zero_eq
-- given
  (L : PeriodPair) :
-- imply
  L.fundamentalParallelogram 0 = ZSpan.fundamentalDomain L.basis :=
-- proof
  fundamentalParallelogram_zero L

end PeriodPair

namespace PeriodPair

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
  L.basis.repr (t₁ • L.ω₁ + t₂ • L.ω₂) i = ![t₁, t₂] i :=
-- proof
  basis_repr_omega L t₁ t₂ i

end PeriodPair

namespace PeriodPair

/--
[FundamentalParallelogram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/FundamentalParallelogram.lean)
-/
@[path]
private lemma mem_fundamentalParallelogram_iff_eq
-- given
  (L : PeriodPair)
  (α z : ℂ) :
-- imply
  z ∈ L.fundamentalParallelogram α ↔
    ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
      z = α + t₁ • L.ω₁ + t₂ • L.ω₂ :=
-- proof
  mem_fundamentalParallelogram_iff L

end PeriodPair


-- created on 2026-10-11
-- updated on 2026-10-26
