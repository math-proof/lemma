import Def.Probability.SymbolicProbability
import Class.Probability.SymbolicProbability
import Theorem.Data.Vector.Basic
import Def.Data.Tensor.Defs.Part4
open MeasureTheory

export Expectation (expectation)


/-!
# Multivariate / container-valued expectation

Lean counterpart of sympy's `symbolic_multivariate_probability` module: instances of
`Expectation` for `List.Vector` and `Tensor`, defined by applying `expectation` on
each component. Scalar instances (`ENNReal`, `EReal`, `ℂ`) live in
`Def.Probability.SymbolicProbability`.
-/

/-- Componentwise expectation on `List.Vector β n`. -/
noncomputable instance {n : ℕ} {β : Type*} [Expectation β] :
    Expectation (List.Vector β n) where
  expectation {_α} _ ν f :=
    List.Vector.ofFn fun i => expectation ν fun a => (f a).get i

/-- Componentwise expectation on `Tensor β s` (via the underlying data vector). -/
noncomputable instance {s : List ℕ} {β : Type*} [Expectation β] :
    Expectation (Tensor β s) where
  expectation {_α} _ ν f :=
    ⟨expectation ν fun a => (f a).data⟩

