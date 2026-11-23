/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean -/
module

public import Def.Combinatorics.JaccardLattice
public import Theorem.Finset.JaccardLattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Def.MathlibExtTest.Combinatorics.JaccardLattice

public section

namespace JaccardLatticeTest

open JaccardLattice

example : 0 < jaccardDist countVal 0 1 := by
  rw [countVal_01]
  norm_num

example : jaccardDist countVal 0 1 + jaccardDist countVal 1 2
    ≥ jaccardDist countVal 0 2 :=
  jaccardDist_triangle countVal_mod countVal_mono countVal_pos 0 2 1

example : jaccardDist countVal 0 1 + jaccardDist countVal 1 2
    > jaccardDist countVal 0 2 := by
  rw [countVal_01, countVal_12, countVal_02]
  norm_num

end JaccardLatticeTest
