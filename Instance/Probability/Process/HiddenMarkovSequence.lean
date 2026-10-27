import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Syntax.Probability.JointRv.Part6
import Def.Data.List.List.Part5
import Instance.Analysis.Real.Numbers
import Def.Fun
import Def.Probability.Process.HiddenMarkovSequence
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- `x[a:b]` for a family of random variables `x i : Ω → α`: the random vector
`ω ↦ (x a ω, …, x (b-1) ω)`. -/
instance {Ω α : Type*} : FunSlice (Ω → α) where
  Out s := Ω → Fin (s.stop.toNat - s.start.toNat) → α
  slice x s := fun ω i => x (i.val + s.start.toNat) ω

