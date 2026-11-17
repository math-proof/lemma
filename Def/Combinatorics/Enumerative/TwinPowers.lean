/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TwinPowers.lean -/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

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
