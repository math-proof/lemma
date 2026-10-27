import Def.Data.List.Slice
import Macro.Data.List.List.Part7
open Lean


partial def Slice.natLitValue? : Syntax → Option Nat
  | `(($n:num)) => some n.getNat
  | `(($n:num : $_)) => some n.getNat
  | `($n:num) => some n.getNat
  | `(OfNat.ofNat $_ $n $_) => natLitValue? n
  | `(Int.ofNat $n) => natLitValue? n
  | _ => none

/-- Infoview: print `getSlice` as Python `base[start:stop:step]`. -/
def Slice.getSliceUnexpand : PrettyPrinter.Unexpander
  | `($_ $x (Slice.mk $start $stop $step))
  | `($_ $x ⟨$start, $stop, $step⟩) =>
    let startZero := natLitValue? start == some 0
    let stepOne := natLitValue? step == some 1
    if stepOne then
      if startZero then
        `($x[:$stop])
      else
        `($x[$start :$stop])
    else if startZero then
      `($x[:$stop :$step])
    else
      `($x[$start :$stop :$step])
  | _ =>
    throw ()

@[app_unexpander List.getSlice]
def List.getSlice.unexpand := Slice.getSliceUnexpand

