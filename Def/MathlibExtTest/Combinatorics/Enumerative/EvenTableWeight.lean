/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/EvenTableWeight.lean -/


import Def.Combinatorics.Enumerative.EvenTableWeight
open scoped BigOperators


namespace MetaMathlibExt

def testFactorFb63c6b5 : ℕ → ℕ := fun m => m + 1

def testTableFb63c6b5 : EvenTable 2 2 where
  entries := fun _ j => j
  isEven := ⟨1, rfl⟩
  rowBijective := fun _ => Function.bijective_id
  colEven := by decide

end MetaMathlibExt
