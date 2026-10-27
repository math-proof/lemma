import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Syntax.Probability.JointRv.Part6
import Def.Data.List.List.Part5
import Instance.Analysis.Real.Numbers
import Def.Fun
import Abbrev.Probability.Process.HiddenMarkovSequence
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- Pairing coercion for two random vectors `x[a:b]`, `y[c:d]` (see `Function.coeProdPi`): the type of
`x[a:b]` is the family `FunSlice.Out (Ω → α) s`, which typeclass search does not unfold to `Ω → …`, so
the generic instances do not fire; these two make a bare pair `(x[:n], y[:m])` an
`Ω → (Fin n → α) × (Fin m → β)`, i.e. `JointRandomSymbol x[:n] y[:m]`, both as a term of function
type (`CoeFun`, used when an `Ω → ?` is expected, e.g. `SinglePSpace π (x[:n], y[:m])`) and as a `Coe`. -/
instance Function.coeProdPiSlice {Ω α β : Type*} {s t : Slice} :
    Coe (FunSlice.Out (Ω → α) s × FunSlice.Out (Ω → β) t) (Ω → FunSlice.Vec α s × FunSlice.Vec β t) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

instance Function.coeFunProdPiSlice {Ω α β : Type*} {s t : Slice} :
    CoeFun (FunSlice.Out (Ω → α) s × FunSlice.Out (Ω → β) t)
      (fun _ => Ω → FunSlice.Vec α s × FunSlice.Vec β t) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

