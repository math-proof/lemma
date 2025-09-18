import stdlib.Basic
#eval mkCtorName ``Lean.Syntax
open Lean

def Lean.Syntax.parity : Syntax → Nat
  | .node _ `Lean.Parser.Attr.simple #[.ident .., .node _ (.str .anonymous "null") #[num]] =>
    num.isNatLit?.getD 0
  | _ =>
    0
