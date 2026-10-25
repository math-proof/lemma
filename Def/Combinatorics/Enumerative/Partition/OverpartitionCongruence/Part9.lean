/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Multiset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Def.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition
import Lemma.Nat.QuadraticForms.ThreeSquares
import Lemma.Real.SpecialFunctions.JacobiTripleProduct
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Def.Analysis.SpecialFunctions.JacobiTripleProduct
import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part8


section

namespace MetaMathlibExt

open PowerSeries

open scoped PowerSeries.WithPiTopology

/-- Theta fibers over `ℤ` match the `True`-subtype fibers. -/
def opcThetaFiber (m : ℕ) :
    {x : Subtype (fun _ : ℤ => True) // x.val.natAbs ^ 2 = m} ≃
      {x : ℤ // x.natAbs ^ 2 = m} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, trivial⟩, x.property⟩
  left_inv x := by obtain ⟨⟨_, _⟩, _⟩ := x; rfl
  right_inv x := by obtain ⟨_, _⟩ := x; rfl

/-- The sigma of square fibers over `ℕ` is `ℤ`. -/
def opcSigmaTheta : (Σ _m : ℕ, {x : ℤ // x.natAbs ^ 2 = _m}) ≃ ℤ where
  toFun p := p.2.val
  invFun x := ⟨x.natAbs ^ 2, x, rfl⟩
  left_inv p := by obtain ⟨m, x, rfl⟩ := p; rfl
  right_inv x := rfl

/-- The mod-5 theta series. -/
noncomputable def opcPhi5 : (ZMod 5)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 5)) opcTheta

/-- The mod-5 twisted overpartition series. -/
noncomputable def opcQ5 : (ZMod 5)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 5)) (PowerSeries.rescale (-1 : ℤ)
    (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))))

end MetaMathlibExt
end
