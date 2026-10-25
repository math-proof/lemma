/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CallanSequence.lean -/


import Structure.Combinatorics.Enumerative.CallanSequence
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Combinatorics.Enumerative.CallanSequence.Part2


namespace MetaMathlibExt

example : (some 0 : Option (Fin 1)) ∈ callan11.blue 0 := by decide

example : (some 0 : Option (Fin 1)) ∈ callan11.red 0 := by decide

example : (none : Option (Fin 1)) ∈ callan11.blue (Fin.last callan11.m) :=
  callan11.blue_mem_star

example : (none : Option (Fin 1)) ∈ callan11.red (Fin.last callan11.m) :=
  callan11.red_mem_star

example (x : Option (Fin 1)) : ∃! i, x ∈ callan11.blue i :=
  callan11.blue_covers x

example (x : Option (Fin 1)) : ∃! i, x ∈ callan11.red i :=
  callan11.red_covers x

end MetaMathlibExt
