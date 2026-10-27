import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Syntax.Probability.JointRv.Part6
import Def.Data.List.List.Part5
import Instance.Analysis.Real.Numbers
import Def.Fun
import Instance.Probability.Process.HiddenMarkovSequence
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- The type of the vector `x[a:b]` of values `Fin (b - a) → α`, as it appears in the type of the random
vector `x[a:b] : Ω → FunSlice.Vec α ⟨a, b, 1⟩`. -/
abbrev FunSlice.Vec (α : Type*) (s : Slice) : Type _ :=
  Fin (s.stop.toNat - s.start.toNat) → α

