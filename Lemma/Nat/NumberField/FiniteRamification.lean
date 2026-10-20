import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.FiniteRamification
open IsDedekindDomain
open NumberField


/--
[finite_ramified_primes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/FiniteRamification.lean)
-/
@[path]
private lemma finite_ramified_primes_eq
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
-- imply
  {p : HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ¬ Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p.asIdeal}.Finite := by
-- proof
  apply NumberField.finite_ramified_primes K L


-- created on 2026-10-20
