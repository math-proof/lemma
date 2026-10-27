import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits.Part7
open Lean
open scoped Topology


def termOfLimPt (x : TSyntax `limPt) : TSyntax `term := ⟨x.raw[0]⟩

