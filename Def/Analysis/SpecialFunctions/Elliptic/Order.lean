/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean -/

import Mathlib.Analysis.Meromorphic.Divisor
import Structure.Analysis.SpecialFunctions.Elliptic.Function
import Lemma.Complex.Function
import Lemma.Complex.FundamentalParallelogram
import Def.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogram
/-!
# Pole sets and elliptic order of meromorphic elliptic functions

For an elliptic function `f` relative to a period pair `L`, this module provides:

* `PeriodPair.poleMultiplicity`, the pointwise pole multiplicity, defined locally from
  `meromorphicOrderAt f z` as the negation (truncated to `ℕ`) of the order. No global
  meromorphicity hypothesis is built into the definition: at points where `f` is not
  even locally meromorphic, the order takes the junk value `0`, so the multiplicity
  is `0` there for an explicitly local reason.
* `PeriodPair.poleSetInFundamentalParallelogram`, the set of poles of `f` lying in
  the fundamental parallelogram with vertex `α`. The parallelogram uses the half-open
  convention `0 ≤ tᵢ < 1` (see `PeriodPair.mem_fundamentalParallelogram_iff`), so the
  vertex `α` belongs to it while the translates `α + ω₁`, `α + ω₂`, `α + ω₁ + ω₂`
  do not.
* `PeriodPair.ellipticOrderInFundamentalParallelogram`, the sum of the pole
  multiplicities over that set, for an arbitrary vertex `α`.
* `PeriodPair.ellipticOrder`, the canonical order at vertex `0`, with an unfolding
  bridge to the arbitrary-vertex count. No independence of the vertex is claimed.
-/


namespace PeriodPair

/-- Pointwise pole multiplicity of `f` at `z`, defined locally from
`meromorphicOrderAt f z`.

The multiplicity is the negation of the order, truncated to `ℕ`: a pole of order
`-n` contributes `n`, while zeros, nonzero values, and points where `f` is not
locally meromorphic (junk order `0`) contribute `0`. Since only the local order is
used, the value at `z` never depends on the behavior of `f` far away from `z`.
-/
noncomputable def poleMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  (-(meromorphicOrderAt f z).untop₀).toNat

/-- The set of poles of `f` in the fundamental parallelogram with vertex `α`: the
points of the parallelogram where the pointwise multiplicity is nonzero. -/
noncomputable def poleSetInFundamentalParallelogram (L : PeriodPair) (f : ℂ → ℂ)
    (α : ℂ) : Set ℂ :=
  {z ∈ L.fundamentalParallelogram α | poleMultiplicity f z ≠ 0}

/-- The elliptic order of `f` counted in the fundamental parallelogram with arbitrary
vertex `α`: the sum of the pointwise pole multiplicities over the finite pole set.
The sum is taken over the finite set supplied by
`PeriodPair.poleSetInFundamentalParallelogram_finite`, which requires the elliptic
hypothesis `hf`. -/
noncomputable def ellipticOrderInFundamentalParallelogram (L : PeriodPair)
    (f : ℂ → ℂ) (α : ℂ) (hf : L.IsEllipticFunction f) : ℕ :=
  ∑ z ∈ (L.poleSetInFundamentalParallelogram_finite hf α).toFinset,
    poleMultiplicity f z

/-- The canonical elliptic order of `f`: the count in the fundamental parallelogram
with vertex `0`. -/
noncomputable def ellipticOrder (L : PeriodPair) (f : ℂ → ℂ)
    (hf : L.IsEllipticFunction f) : ℕ :=
  L.ellipticOrderInFundamentalParallelogram f 0 hf

end PeriodPair
