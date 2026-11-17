/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CallanSequence.lean -/
module

public import Structure.Combinatorics.Enumerative.CallanSequence
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.FinCases
public import Def.MathlibExtTest.Combinatorics.Enumerative.CallanSequence

public section

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
