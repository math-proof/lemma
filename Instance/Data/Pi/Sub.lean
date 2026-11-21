module

public import Mathlib.Tactic.TypeStar

/-!
# Scalar-broadcast subtraction for functions

`f - a` with `f : ι → α` and `a : α` subtracts the same scalar from every component, the plain
function analogue of `HSub (Matrix m n α) α (Matrix m n α)`. The right operand of `-` is
elaborated as the scalar `α`, so the second type of the instance must be `α`: spelling it
`ι → α` would mean the scalar has to be read as the constant function `fun _ => a`, which is not
available for a general scalar (it is why `(s : ℝ) • 1` used to be needed instead of `s`). The Pi
instance `HSub (∀ i, α i) (∀ i, β i) (∀ i, γ i)` requires the right operand to be a function, so
it does not cover this case.

This is a broadcast, like the matrix and vector scalar instances: there is no per-index
`f i - a i` reading. Same-type function subtraction `f - g` still goes through the Pi instance;
when both instances match (when `α` is itself a function type and the right operand is a
function), they produce the same pointwise term, so no priority annotation is needed.

The expression tree elaborator does consult this heterogeneous instance: in
`Lemma/Real/Grad/Softmax/eq/Mul/Softmax/vector/using/Stack.lean`,
`∂[x] F x - ((F x).softmax ⬝ᵥ ∂[x] F x)` with `F : ℝ → (Fin n → ℝ)` elaborates because of it.
-/

@[expose] public section

namespace Pi

instance instHSubScalar {ι α : Type*} [Sub α] : HSub (ι → α) α (ι → α) where
  hSub f a i := f i - a

/-- Component `i` of the scalar-broadcast subtraction. This is definitional, so `rfl` also
closes goals of this shape. -/
@[simp] theorem sub_scalar_apply {ι α : Type*} [Sub α] (f : ι → α) (a : α) (i : ι) :
    (f - a) i = f i - a :=
  rfl

end Pi
