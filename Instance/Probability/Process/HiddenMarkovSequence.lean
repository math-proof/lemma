module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Def.Data.List.List.Basic
public import Instance.Analysis.Real.Numbers
public import Abbrev.Probability.Process.HiddenMarkovSequence
public import Def.Probability.JointRv
public import Notation.Fun

@[expose] public section

open scoped ENNReal.ToRealCoe


/-- `x[a:b]` for a family of random variables `x i : Ω → α`: the random vector
`ω ↦ (x a ω, …, x (b-1) ω)`. -/
instance {Ω α : Type*} : FunSlice (Ω → α) where
  Out s := Ω → Fin (s.stop.toNat - s.start.toNat) → α
  slice x s := fun ω i => x (i.val + s.start.toNat) ω


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

/-- Pairing coercion for a random variable and a random vector `x`, `y[c:d]` (see `Function.coeProdPi`): the type of
`y[c:d]` is the family `FunSlice.Out (Ω → β) s`, which typeclass search does not unfold to `Ω → …`, so
the generic instances do not fire; these two make a bare pair `(x, y[:n])` an
`Ω → α × FunSlice.Vec β s`, i.e. `JointRandomSymbol x y[:n]`, both as a term of function
type (`CoeFun`, used when an `Ω → ?` is expected, e.g. `SinglePSpace π (s[k], s[:k])`) and as a `Coe`. -/
instance Function.coeProdPiGetSlice {Ω α β : Type*} {s : Slice} :
    Coe ((Ω → α) × FunSlice.Out (Ω → β) s) (Ω → α × FunSlice.Vec β s) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

instance Function.coeFunProdPiGetSlice {Ω α β : Type*} {s : Slice} :
    CoeFun ((Ω → α) × FunSlice.Out (Ω → β) s)
      (fun _ => Ω → α × FunSlice.Vec β s) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

/-- Pairing coercion for a random vector `x[a:b]` and a random variable `y` (see `Function.coeProdPi`): the type of
`x[a:b]` is the family `FunSlice.Out (Ω → α) s`, which typeclass search does not unfold to `Ω → …`, so
the generic instances do not fire; these two make a bare pair `(x[:n], y)` an
`Ω → FunSlice.Vec α s × β`, i.e. `JointRandomSymbol x[:n] y`, both as a term of function
type (`CoeFun`, used when an `Ω → ?` is expected, e.g. `SinglePSpace π (s[:k], Z)`) and as a `Coe`. -/
instance Function.coeProdPiSliceGet {Ω α β : Type*} {s : Slice} :
    Coe (FunSlice.Out (Ω → α) s × (Ω → β)) (Ω → FunSlice.Vec α s × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

instance Function.coeFunProdPiSliceGet {Ω α β : Type*} {s : Slice} :
    CoeFun (FunSlice.Out (Ω → α) s × (Ω → β))
      (fun _ => Ω → FunSlice.Vec α s × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩
