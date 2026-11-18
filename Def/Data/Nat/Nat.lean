module

public import Mathlib.Tactic

@[expose] public section

open Lean


@[app_unexpander Min.min]
meta def Min.min.unexpand : PrettyPrinter.Unexpander
  | `($_ $m:term $n:term) =>
    `($m ⊓ $n)
  | _ =>
    throw ()

@[app_unexpander Max.max]
meta def Max.max.unexpand : PrettyPrinter.Unexpander
  | `($_ $m:term $n:term) =>
    `($m ⊔ $n)
  | _ =>
    throw ()

