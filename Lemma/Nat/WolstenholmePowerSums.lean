import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.WolstenholmePowerSums
open scoped BigOperators
open MetaMathlibExt


/--
[wolstenholme_harmonic_power_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WolstenholmePowerSums.lean)
-/
@[path]
private lemma wolstenholme_harmonic_power_sum_eq
  {ν p : ℕ}
-- given
  (hν : 1 ≤ ν)
  (hνodd : Odd ν)
  (hp : p.Prime)
  (hpν : ν + 4 ≤ p) :
-- imply
  ∑ t ∈ Finset.Icc 1 (p - 1), (((t : ZMod (p ^ 2)) ^ ν)⁻¹) = 0 := by
-- proof
  apply MetaMathlibExt.wolstenholme_harmonic_power_sum ν p hν hνodd hp hpν


-- created on 2026-10-20
