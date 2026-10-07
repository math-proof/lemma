import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import sympy.stats.joint_rv
import stdlib.List
import sympy.core.numbers

/-- Sequential (first-order, hidden) Markov structure of the prefix joint probabilities used by the
py CRF lemmas.  `P t ys` is `Pr(x[:t+1] = x_obs[:t+1], y[:t+1] = ys[:t+1])` for the fixed observed
sequence, `π a = Pr(y[0] = a)`, `T a b = Pr(y[i] = b | y[i-1] = a)` (time-homogeneous) and
`E i b = Pr(x[i] = x_obs[i] | y[i] = b)`.  The py independence assumptions
(`x[k] | x[:k] & y[:k] = x[k]`, `y[k] | y[:k] = y[k] | y[k-1]`, `y[k] | x[:k] = y[k]`) are used in py
only through the one-step factorization recorded here. -/
def IsHiddenMarkovSeq {Y : Type*} (P : ℕ → (ℕ → Y) → ℝ) (π : Y → ℝ) (T : Y → Y → ℝ) (E : ℕ → Y → ℝ) : Prop :=
  ∀ ys : ℕ → Y, P 0 ys = E 0 (ys 0) * π (ys 0) ∧
    ∀ t, P (t + 1) ys = P t ys * (T (ys t) (ys (t + 1)) * E (t + 1) (ys (t + 1)))


open MeasureTheory
open scoped ENNReal.ToRealCoe

/-- Generic form of `IsHiddenMarkovPr`: the one-step factorization of an abstract prefix-probability family `P`
(`IsHiddenMarkovPr` is this with `P t ys := Pr(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])`).
Sequential (first-order, hidden) Markov structure of the prefix joint probabilities used by the
py CRF lemmas, stated directly in probability notation.  `y i : Ω → Y` are the hidden labels,
`x i : Ω → X` the observations and `xo i` the fixed observed value of `x i`.
`P t ys` is `Pr(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])` and satisfies the one-step factorization

  `P 0 ys = Pr(x[0] = xo[0] | y[0] = ys[0]) * Pr(y[0] = ys[0])`,
  `P (t+1) ys = P t ys * (Pr(y[t+1] = ys[t+1] | y[t] = ys[t]) * Pr(x[t+1] = xo[t+1] | y[t+1] = ys[t+1]))`

which is all the py independence assumptions
(`x[k] | x[:k] & y[:k] = x[k]`, `y[k] | y[:k] = y[k] | y[k-1]`, `y[k] | x[:k] = y[k]`) are used for. -/
def IsHiddenMarkovFac {Ω Y X : Type*} [MeasurableSpace Ω] [ReferenceMeasure Y] [ReferenceMeasure X]
    (π : Measure Ω) (x : ℕ → Ω → X) (y : ℕ → Ω → Y) (xo : ℕ → X) (P : ℕ → (ℕ → Y) → ℝ)
    [∀ i, SinglePSpace π (y i)] [∀ i j, SinglePSpace π (x i, y j)]
    [∀ i j, SinglePSpace π (y i, y j)] : Prop :=
  ∀ ys : ℕ → Y,
    P 0 ys = (ℙ[π]((x 0) = xo 0 | (y 0) = ys 0) : ℝ) * (ℙ[π]((y 0) = ys 0) : ℝ) ∧
    ∀ t, P (t + 1) ys = P t ys * ((ℙ[π]((y (t + 1)) = ys (t + 1) | (y t) = ys t) : ℝ) *
      (ℙ[π]((x (t + 1)) = xo (t + 1) | (y (t + 1)) = ys (t + 1)) : ℝ))


/-- Slicing of a function `ℕ → β`, dispatched on its value type `β` (instances: `β = α` for a plain
sequence `f : ℕ → α`, and `β = Ω → α` for a family of random variables `x : ℕ → Ω → α`).  Used by
`Function.getSlice`, i.e. by the shared `x[start:stop]` syntax of `stdlib.List`. -/
class FunSlice (β : Type*) where
  Out : Slice → Type*
  slice : (ℕ → β) → (s : Slice) → Out s

/-- `f[a:b]` for `f : ℕ → α`: the vector `(f a, …, f (b-1)) : Fin (b - a) → α`. -/
instance (priority := low) {α : Type*} : FunSlice α where
  Out s := Fin (s.stop.toNat - s.start.toNat) → α
  slice f s := fun i => f (i.val + s.start.toNat)

/-- `x[a:b]` for a family of random variables `x i : Ω → α`: the random vector
`ω ↦ (x a ω, …, x (b-1) ω)`. -/
instance {Ω α : Type*} : FunSlice (Ω → α) where
  Out s := Ω → Fin (s.stop.toNat - s.start.toNat) → α
  slice x s := fun ω i => x (i.val + s.start.toNat) ω

/-- The type of the vector `x[a:b]` of values `Fin (b - a) → α`, as it appears in the type of the random
vector `x[a:b] : Ω → FunSlice.Vec α ⟨a, b, 1⟩`. -/
abbrev FunSlice.Vec (α : Type*) (s : Slice) : Type _ :=
  Fin (s.stop.toNat - s.start.toNat) → α

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

/-- Python slicing of a function on `ℕ` (`f[:n]`, `f[a:b]`, via the shared `x[start:stop]` syntax of
`stdlib.List`, which expands to `x.getSlice ⟨start, stop, 1⟩`).  For a family of random
variables `x : ℕ → Ω → α` it is the random vector `ω ↦ (x a ω, …, x (b-1) ω)`, for a plain
sequence `f : ℕ → α` it is `(f a, …, f (b-1)) : Fin (b - a) → α`.  Only unit step is supported. -/
def Function.getSlice {β : Type*} [FunSlice β] (x : ℕ → β) (s : Slice) : FunSlice.Out β s :=
  FunSlice.slice x s

@[app_unexpander Function.getSlice]
def Function.getSlice.unexpand := Slice.getSliceUnexpand


/-! ### Joint history of several processes: `(x, y, …)[:n]`

`(r, s, a)[:n]` (a tuple of processes `r s a : ℕ → Ω → _`, prefix slice) is the joint history random
vector `fun ω (i : Fin n) ↦ (r i, s i, a i) ω : Ω → Fin n → ℝ × S × A`, i.e. the vector of the joint
random variables `(r i, s i, a i)` (`JointRandomSymbol`, see `Function.coeProdPi3R`) for `i < n`; it
is syntactically that term, so it can replace it in statements without changing proofs. For pairs and
triples the components are packed by the tuple coercion `(x i, y i) ω` / `(x i, y i, z i) ω`, for
four or more components by right-nested `JointRandomSymbol`. Only a literal tuple receiver is
rewritten; every other `x[:n]` (lists, vectors, tensors, a single process `x[:n]`, a parenthesized
`(e)[:n]`) keeps the generic `x.getSlice ⟨0, n, 1⟩` of `stdlib.List`. Used e.g. as the history in
`(a n, r n, s (n + 1)) ⟂ᵢ[π] (r, s, a)[:n] | s n`.
-/
open Lean in
macro_rules
  | `(($x, $ys,*)[:$n]) => do
    let comps ← (#[x] ++ ys.getElems).mapM fun z => `($z i)
    let tuple : Term ← if comps.size ≤ 3 then
        `(($(comps[0]!), $(comps.extract 1 comps.size),*))
      else
        comps.pop.foldrM (fun c acc => `(JointRandomSymbol $c $acc)) comps.back!
    `(fun ω (i : Fin $n) ↦ $tuple ω)
/-- The py first-order hidden Markov assumptions in probability notation (py `markov_assumptions` + `Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.IsDiscreteHMM`):
for every label sequence `ys`,

  `Pr(x[:1] = xo[:1], y[:1] = ys[:1]) = Pr(x[0] = xo[0] | y[0] = ys[0]) * Pr(y[0] = ys[0])`,
  `Pr(x[:t+2] = xo[:t+2], y[:t+2] = ys[:t+2]) = Pr(x[:t+1] = xo[:t+1], y[:t+1] = ys[:t+1])
      * (Pr(y[t+1] = ys[t+1] | y[t] = ys[t]) * Pr(x[t+1] = xo[t+1] | y[t+1] = ys[t+1]))`. -/
def IsHiddenMarkovPr {Ω Y X : Type*} [MeasurableSpace Ω] [ReferenceMeasure Y] [ReferenceMeasure X]
    [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
    (π : Measure Ω) (x : ℕ → Ω → X) (y : ℕ → Ω → Y) (xo : ℕ → X)
    [∀ i, SinglePSpace π (y i)] [∀ i j, SinglePSpace π (x i, y j)]
    [∀ i j, SinglePSpace π (y i, y j)]
    [∀ n, SinglePSpace π (x[:n], y[:n])] : Prop :=
  ∀ ys : ℕ → Y,
    (ℙ[π](x[:0 + 1] = xo[:0 + 1] ∧ y[:0 + 1] = ys[:0 + 1]) : ℝ) =
        (ℙ[π]((x 0) = xo 0 | (y 0) = ys 0) : ℝ) * (ℙ[π]((y 0) = ys 0) : ℝ) ∧
    ∀ t : ℕ, (ℙ[π](x[:t + 1 + 1] = xo[:t + 1 + 1] ∧ y[:t + 1 + 1] = ys[:t + 1 + 1]) : ℝ) =
      (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ) *
        ((ℙ[π]((y (t + 1)) = ys (t + 1) | (y t) = ys t) : ℝ) *
          (ℙ[π]((x (t + 1)) = xo (t + 1) | (y (t + 1)) = ys (t + 1)) : ℝ))


-- created on 2026-09-27
