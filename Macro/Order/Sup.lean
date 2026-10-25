import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Image
import Def.Order.Sup


open Lean in
macro_rules
  | `(sup[$xs:supBinder,*] $e < ∞) => do
    let binders ← xs.getElems.mapM parseSupBinder
    let f ← mkRangeFun binders e
    `(BddAbove (Set.range $f))
  | `(sup[$xs:supBinder,* | $c] $e < ∞) => do
    let binders ← xs.getElems.mapM parseSupBinder
    let f ← mkRangeFun binders e
    let condFun ← mkRangeFun binders c
    `(BddAbove ($f '' {p | $condFun p}))

