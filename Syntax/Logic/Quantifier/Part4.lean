import Lean
import Macro.Logic.Quantifier.Part3
open Lean (Macro explicitBinders)


syntax "∃" explicitBinders "∈" term "|" term ", " term : term

