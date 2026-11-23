module

public import Instance.Data.Tensor.Tensor.Part2
public import Syntax.Data.Tensor.Stack.Part3

@[expose] public meta section

open Lean


-- Unexpander to convert Stack expressions back to custom syntax
@[app_unexpander Stack]
meta def Stack.unexpand : PrettyPrinter.Unexpander
  | `($_ $n:term fun $x:ident => $body) =>
    `([$x:ident < $n] $body)
  | _ =>
    throw ()

/-- Infoview: print `([i < n] f i).sum 0` as `∑ i < n, f i`. -/
@[app_unexpander Tensor.sum]
meta def Tensor.sum.unexpand : PrettyPrinter.Unexpander
  | `($_ $X 0) =>
    match X with
    | `([$x < $n] $body) =>
      `(∑ $x < $n, $body)
    | _ =>
      throw ()
  | _ =>
    throw ()

/-- Infoview: print `([i < n] f i).prod 0` as `∏ i < n, f i`. -/
@[app_unexpander Tensor.prod]
meta def Tensor.prod.unexpand : PrettyPrinter.Unexpander
  | `($_ $X 0) =>
    match X with
    | `([$x < $n] $body) =>
      `(∏ $x < $n, $body)
    | _ =>
      throw ()
  | _ =>
    throw ()

