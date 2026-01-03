import Mathlib.Tactic
open Lean


instance : Coe Bool ℕ where
  coe b := b.toNat

instance [NatCast α] : Coe ℕ α where
  coe n := (n : α)

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
