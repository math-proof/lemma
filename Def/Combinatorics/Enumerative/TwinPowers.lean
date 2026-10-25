/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TwinPowers.lean -/

import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


section

namespace MetaMathlibExt

def dCoeffNat (l j : ℕ) : ℕ :=
  Nat.choose (l + j) (2 * j) + 2 * Nat.choose (l + j) (2 * j + 1)

noncomputable def Pd (l : ℕ) : PowerSeries ℝ :=
  Finset.sum (Finset.range (l + 1)) (fun j : ℕ =>
    ((dCoeffNat l j : ℕ) : PowerSeries ℝ)
      * (PowerSeries.X : PowerSeries ℝ) ^ j)

end MetaMathlibExt
end
