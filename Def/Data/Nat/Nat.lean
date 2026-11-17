module

public import Mathlib.Tactic
public import Instance.Data.Nat.Nat

@[expose] public section

open Lean


@[app_unexpander Min.min]
def Min.min.unexpand : PrettyPrinter.Unexpander
  | `($_ $m:term $n:term) =>
    `($m ⊓ $n)
  | _ =>
    throw ()

@[app_unexpander Max.max]
def Max.max.unexpand : PrettyPrinter.Unexpander
  | `($_ $m:term $n:term) =>
    `($m ⊔ $n)
  | _ =>
    throw ()

