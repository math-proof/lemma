import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RiordanArrayInverse
open MetaMathlibExt


/--
[riordan_array_inverse_via_a_and_z_sequences_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanArrayInverse.lean)
-/
@[path]
private lemma riordan_array_inverse_via_a_and_z_sequences_general_eq
  :
-- imply
  {K : Type*} [Field K]
    (g f A Z fInv : PowerSeries K)
    (d₀₀ : K)
    (hd₀₀ : PowerSeries.constantCoeff g = d₀₀)
    (hd₀₀_ne : d₀₀ ≠ 0)
    (hf₀ : PowerSeries.constantCoeff f = 0)
    (hA₀ : PowerSeries.constantCoeff A ≠ 0)
    (hfInv₀ : PowerSeries.constantCoeff fInv = 0)
    (hA : f = (PowerSeries.X : PowerSeries K) * PowerSeries.subst f A)
    (hcomp_left : PowerSeries.subst fInv f = (PowerSeries.X : PowerSeries K))
    (hZ : g = PowerSeries.C (R := by
-- proof
  apply MetaMathlibExt.riordan_array_inverse_via_a_and_z_sequences_general

/--
[riordan_array_inverse_via_a_and_z_sequences](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanArrayInverse.lean)
-/
@[path]
private lemma riordan_array_inverse_via_a_and_z_sequences_eq
  :
-- imply
  {K : Type*} [Field K]
    (g f A Z fInv : PowerSeries K)
    (d₀₀ : K)
    (hd₀₀ : PowerSeries.constantCoeff g = d₀₀)
    (hd₀₀_ne : d₀₀ ≠ 0)
    (hf₀ : PowerSeries.constantCoeff f = 0)
    (hA₀ : PowerSeries.constantCoeff A ≠ 0)
    (hfInv₀ : PowerSeries.constantCoeff fInv = 0)
    (hA : f = (PowerSeries.X : PowerSeries K) * PowerSeries.subst f A)
    (hcomp_left : PowerSeries.subst fInv f = (PowerSeries.X : PowerSeries K))
    (hcomp_right : PowerSeries.subst f fInv = (PowerSeries.X : PowerSeries K))
    (hZ : g = PowerSeries.C (R := by
-- proof
  apply MetaMathlibExt.riordan_array_inverse_via_a_and_z_sequences


-- created on 2026-10-20
