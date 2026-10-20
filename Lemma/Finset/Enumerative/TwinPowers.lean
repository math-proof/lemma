import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TwinPowers
open MetaMathlibExt


/--
[twin_powers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TwinPowers.lean)
-/
@[path]
private lemma twin_powers_eq
  {l : ℕ}
  {g Bf Bh : PowerSeries ℝ}
-- given
  (hg : PowerSeries.constantCoeff g ≠ 0) :
-- imply
  let Xr : PowerSeries ℝ := by
-- proof
  apply MetaMathlibExt.twin_powers l g Bf Bh hg


-- created on 2026-10-20
