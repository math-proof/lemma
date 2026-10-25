import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Def.Algebra.BigOperators.Summations


open Lean in
macro_rules (kind := sumAtGetElem)
  | `(∑ $x:ident[$t], $body) => expandSumAt x t body false

open Lean in
macro_rules (kind := sumAt)
  | `(∑ $x:ident $t, $body) => expandSumAt x t body true

