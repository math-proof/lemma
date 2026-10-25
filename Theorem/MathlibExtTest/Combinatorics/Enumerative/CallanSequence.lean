/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CallanSequence.lean -/


import Structure.Combinatorics.Enumerative.CallanSequence
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Combinatorics.Enumerative.CallanSequence


namespace MetaMathlibExt

example : callan00.m = 0 := rfl

example : callan00.m ≤ 0 := callan00.m_le_n

example : (none : Option (Fin 0)) ∈ callan00.blue (Fin.last callan00.m) :=
  callan00.blue_mem_star

example : (none : Option (Fin 0)) ∈ callan00.red (Fin.last callan00.m) :=
  callan00.red_mem_star

example (x : Option (Fin 0)) : ∃! i, x ∈ callan00.blue i :=
  callan00.blue_covers x

example (x : Option (Fin 0)) : ∃! i, x ∈ callan00.red i :=
  callan00.red_covers x

end MetaMathlibExt
