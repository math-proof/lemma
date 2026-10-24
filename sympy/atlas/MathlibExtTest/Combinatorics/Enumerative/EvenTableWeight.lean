/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/EvenTableWeight.lean -/


import sympy.atlas.Combinatorics.Enumerative.EvenTableWeight

open scoped BigOperators

namespace MetaMathlibExt

private def testFactorFb63c6b5 : ℕ → ℕ := fun m => m + 1

private def testTableFb63c6b5 : EvenTable 2 2 where
  entries := fun _ j => j
  isEven := ⟨1, rfl⟩
  rowBijective := fun _ => Function.bijective_id
  colEven := by decide

example : evenTableWeight testFactorFb63c6b5 testTableFb63c6b5 = 9 := rfl

example : evenTableWeight testFactorFb63c6b5 testTableFb63c6b5 =
    ∏ j, columnWeight 2 testFactorFb63c6b5
      (List.ofFn fun i => testTableFb63c6b5.entries i j) := rfl

end MetaMathlibExt
