/-
Author: @akiezun, Avocado
-/

import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry13Ramanujanfactorial
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/


namespace Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

noncomputable def dblR (t : ℝ) (c : ℕ+ × ℕ+) : ℝ :=
  if (c.2:ℕ) % 2 = (c.1:ℕ) % 2 ∧ (c.1:ℕ) ≤ (c.2:ℕ) then
    if (c.1:ℕ) = (c.2:ℕ) then signW c.1 * t ^ ((c.1:ℕ) * (c.2:ℕ))
    else 2 * signW c.1 * t ^ ((c.1:ℕ) * (c.2:ℕ))
  else 0

noncomputable def singleR (t : ℝ) (k : ℕ+) : ℝ :=
  signW k * (t ^ ((k:ℕ)^2) * (1 + t ^ (2*(k:ℕ))) / (1 - t ^ (2*(k:ℕ))))

noncomputable def arithEquiv (k : ℕ+) :
    ℕ ≃ { j : ℕ+ // (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) } where
  toFun m :=
    let v : ℕ := (k:ℕ) + 2 * m
    have hkpos : 0 < (k:ℕ) := k.2
    have hv : 0 < v := by omega
    have hmod : v % 2 = (k:ℕ) % 2 := by omega
    have hle : (k:ℕ) ≤ v := by omega
    ⟨⟨v, hv⟩, hmod, hle⟩
  invFun j := (((j:ℕ+) : ℕ) - (k:ℕ)) / 2
  left_inv m := by
    have hkpos : 0 < (k:ℕ) := k.2
    simp only
    have : ((k:ℕ) + 2 * m - (k:ℕ)) / 2 = m := by omega
    exact this
  right_inv j := by
    obtain ⟨⟨jv, hjpos⟩, hmod, hle⟩ := j
    simp only [PNat.mk_coe] at hmod hle ⊢
    have hval : (k:ℕ) + 2 * ((jv - (k:ℕ)) / 2) = jv := by omega
    apply Subtype.ext
    apply PNat.eq
    exact hval

end
end Entry13Ramanujanfactorial
end Ramanujan.Part1Ch6
