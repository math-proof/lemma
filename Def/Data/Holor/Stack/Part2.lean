import Instance.Data.Holor.Tensor.Part2
import Macro.Data.Holor.Stack.Part3
open Lean


-- Unexpander to convert Stack expressions back to custom syntax
@[app_unexpander Stack]
def Stack.unexpand : PrettyPrinter.Unexpander
  | `($_ $n:term fun $x:ident => $body) =>
    `([$x:ident < $n] $body)
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

/-- Infoview: print `([i < n] f i).prod 0` as `∏ i < n, f i`. -/
@[app_unexpander Tensor.prod]
def Tensor.prod.unexpand : PrettyPrinter.Unexpander
  | `($_ $X 0) =>
    match X with
    | `([$x < $n] $body) =>
      `(∏ $x < $n, $body)
    | _ =>
      throw ()
  | _ =>
    throw ()

