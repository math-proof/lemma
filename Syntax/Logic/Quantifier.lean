import Lean
open Lean (Macro explicitBinders)


syntax "∀" ident "|" term ", " term : term

