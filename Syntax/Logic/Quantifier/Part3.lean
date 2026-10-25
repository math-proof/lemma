import Lean
import Macro.Logic.Quantifier.Part2
open Lean (Macro explicitBinders)


syntax "∃" explicitBinders "|" term ", " term : term

