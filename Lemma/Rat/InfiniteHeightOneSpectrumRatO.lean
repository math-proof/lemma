import Mathlib
import sympy.Basic
open IsDedekindDomain NumberField


/--
[infinite_heightOneSpectrum_ratO]
-/
@[path]
private lemma main :
-- imply
  Infinite (HeightOneSpectrum (𝓞 ℚ)) := by
-- proof
  apply Infinite.of_injective (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective


-- created on 2026-10-24
