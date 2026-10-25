import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Def.Order.Max


open Lean in
macro_rules
  | `(max[$xs:maxBinder,*] $e) => do
    let binders ← xs.getElems.mapM parseMaxBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      r ← match ty? with
        | some ty => `(Finset.univ.sup' Finset.univ_nonempty (fun ($x:ident : $ty) => $r))
        | none => `(Finset.univ.sup' Finset.univ_nonempty (fun $x:ident => $r))
    pure r
  | `(max[$xs:maxBinder,* : $T] $e) => do
    let binders ← xs.getElems.mapM parseMaxBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      let ty := ty?.getD T
      r ← `(Finset.univ.sup' Finset.univ_nonempty (fun ($x:ident : $ty) => $r))
    pure r


