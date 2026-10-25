/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PolarDensity.lean -/

import Def.NumberTheory.NumberField.PartialDedekindZeta
import Lemma.Nat.NumberField.PartialDedekindZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Complex.ReImTopology
open Filter Topology NumberField IsDedekindDomain

/-!
# Polar density of sets of height-one primes

This module introduces the corrected polar-density API for `ATLAS NumberTheoryI N409`.

The key semantic correction: `MeromorphicAt` is asserted of `F`, the actual
meromorphic continuation, never of the raw Euler-product `tprod`.
The raw Euler product is only used as a pointwise germ on the right half-plane
`{z : ℂ | 1 < z.re}` near `1`.
-/


namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- Polar density of a set of height-one primes, via a meromorphic continuation.

`HasPolarDensity S ρ` asserts the existence of a positive exponent `n : ℕ+`, a
pole order `m : ℤ`, and an actual meromorphic continuation `F : ℂ → ℂ` such that
`F` is meromorphic at `1`, agrees with the pointwise `n`-th power of the partial
Dedekind zeta function on the right-half-plane germ at `1`, has
`meromorphicOrderAt F 1 = -m`, and `ρ = m / n`. -/
def HasPolarDensity (S : Set (HeightOneSpectrum (𝓞 K))) (ρ : ℚ) : Prop :=
  ∃ (n : ℕ+) (m : ℤ) (F : ℂ → ℂ),
    MeromorphicAt F (1 : ℂ) ∧
      F =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}]
        (fun s => NumberField.partialDedekindZeta K S s ^ (n : ℕ)) ∧
      meromorphicOrderAt F (1 : ℂ) = (↑(-m) : WithTop ℤ) ∧
      ρ = (m : ℚ) / (n : ℚ)

end NumberField.Set
