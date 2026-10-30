import Notation.Fun
open Lean


syntax:max term noWs "[:" withoutPosition(term:60) "]" : term

macro_rules
  | `($x[:$stop]) => `(($x).getSlice ⟨(0 : ℤ), ($stop : ℤ), (1 : ℤ)⟩)

syntax:max term noWs "[::" withoutPosition(term:60) "]" : term



macro_rules
  | `($x[::$step]) => `(($x).getSlice ⟨(if $step < 0 then -1 else 0 : ℤ), (if $step < 0 then -($x).length.succ else ($x).length : ℤ), ($step : ℤ)⟩)

syntax:max term noWs "[" withoutPosition(term:60) ":" withoutPosition(term:80) ":]" : term



macro_rules
  | `($x[$start :$stop]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩)
  | `($x[$start :$stop :]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), (1 : ℤ)⟩)

syntax:max term noWs "[:" withoutPosition(term:60) ":" withoutPosition(term:60) "]" : term



macro_rules
  | `($x[:$stop :$step]) => `(($x).getSlice ⟨(if $step < 0 then -1 else 0 : ℤ), ($stop : ℤ), ($step : ℤ)⟩)

syntax:max term noWs "[" withoutPosition(term:60) "::" withoutPosition(term:60) "]" : term



macro_rules
  | `($x[$start ::$step]) => `(($x).getSlice ⟨($start : ℤ), (if $step < 0 then -($x).length.succ else ($x).length : ℤ), ($step : ℤ)⟩)

syntax:max term noWs "[" withoutPosition(term:60) ":" withoutPosition(term:60) ":" withoutPosition(term:60) "]" : term



macro_rules
  | `($x[$start :$stop :$step]) => `(($x).getSlice ⟨($start : ℤ), ($stop : ℤ), ($step : ℤ)⟩)

declare_syntax_cat slice_arg

syntax withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" : slice_arg

syntax ":" withoutPosition(term:60) : slice_arg

syntax "::" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" withoutPosition(term:60) ":" : slice_arg

syntax ":" withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:68) "::" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg

syntax:max term noWs "[" slice_arg "," slice_arg,+ "]" : term



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
