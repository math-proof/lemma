import Lean
import Macro.Logic.Quantifier
open Lean (Macro explicitBinders)


syntax "∀" ident "∈" term "|" term ", " term : term

