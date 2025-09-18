import sympy.tensor.tensor

/--
[stack](https://docs.pytorch.org/docs/stable/generated/torch.stack.html)
-/
def Stack (n : ℕ) (f : Fin n → Tensor α shape) : Tensor α (n :: shape) :=
  Tensor.fromVector ((List.Vector.range n).map f)


syntax "[" ident "<" term "]" term:67 : term
macro_rules
  | `([$x < $n] $body) => `(Stack $n fun $x => $body)


-- Unexpander to convert Stack expressions back to custom syntax
@[app_unexpander Stack]
def unexpandStack : Lean.PrettyPrinter.Unexpander
  | `($_ $n:term fun $x:ident => $body) =>
    -- Reconstruct the custom syntax [x < n] body
    `([$x < $n] $body)
  | _ =>
    -- If pattern doesn't match, fall back to default printing
    throw ()
