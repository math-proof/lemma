module

public import Structure.Data.Tensor.Defs

@[expose] public section
open Bool Nat Int List Lean


@[app_unexpander Tensor.mk]
meta def Tensor.mk.unexpand : PrettyPrinter.Unexpander
  | `($_ $data) => `(⟨$data⟩)
  | _  =>
    throw ()


def Tensor.length  (X : Tensor α shape)  : ℕ :=
  match shape with
  | [] => 0
  | length :: _ => length

