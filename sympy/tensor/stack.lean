import sympy.tensor.tensor
open Lean

/--
[stack](https://docs.pytorch.org/docs/stable/generated/torch.stack.html)
-/
def Stack (n : ℕ) (f : Fin n → Tensor α shape) : Tensor α (n :: shape) :=
  Tensor.fromVector ((List.Vector.range n).map f)


syntax "[" ident "<" term "]" term:67 : term
macro_rules
  | `([$x < $n] $body) => `(Stack $n fun $x => $body)

/--
Tensor sum along axis 0 of a stack: `∑ i < n, f i` means `([i < n] f i).sum 0`.
Uses priority above Mathlib's bounded `∑ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∑ " ident "<" term ", " term:67 : term
macro_rules
  | `(∑ $x < $n, $body) => `(([ $x < $n ] $body).sum 0)


-- Unexpander to convert Stack expressions back to custom syntax
@[app_unexpander Stack]
def Stack.unexpand : PrettyPrinter.Unexpander
  | `($_ $n:term fun $x:ident => $body) =>
    `([$x < $n] $body)
  | _ =>
    throw ()

/-- Infoview: print `([i < n] f i).sum 0` as `∑ i < n, f i`. -/
@[app_unexpander Tensor.sum]
def Tensor.sum.unexpand : PrettyPrinter.Unexpander
  | `($_ $X 0) =>
    match X with
    | `([$x < $n] $body) =>
      `(∑ $x < $n, $body)
    | _ =>
      throw ()
  | _ =>
    throw ()
