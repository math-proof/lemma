module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Multiset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Def.Combinatorics.Enumerative.Partition.Overpartition
public import Theorem.Nat.Enumerative.Partition.Overpartition
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Lemma.Real.SpecialFunctions.JacobiTripleProduct
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Def.Analysis.SpecialFunctions.JacobiTripleProduct
public import Theorem.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
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
