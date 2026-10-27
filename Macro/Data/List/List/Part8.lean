import Def.Data.List.Slice
import Syntax.Data.List.List.Part8
open Lean


macro_rules
  | `($x[ $first, $rest,* ]) => do
    let indices := #[first] ++ rest
    let mut x := x
    for idx in indices do
      x ←
        match idx with
        | `(slice_arg| $t:term) =>
          `($x[$t])
        | `(slice_arg| $start:term :) =>
          `($x[$start :])
        | `(slice_arg| :$stop) =>
          `($x[:$stop])
        | `(slice_arg| ::$step) =>
          `($x[::$step])
        | `(slice_arg| $start:term : $stop)
        | `(slice_arg| $start:term : $stop :) =>
          `($x[$start :$stop])
        | `(slice_arg| : $stop:term : $step) =>
          `($x[: $stop :$step])
        | `(slice_arg| $start:term :: $step:term) =>
          `($x[$start :: $step])
        | `(slice_arg| $start:term : $stop : $step)  =>
          `($x[$start :$stop :$step])
        | _ =>
          Macro.throwUnsupported
    return x

