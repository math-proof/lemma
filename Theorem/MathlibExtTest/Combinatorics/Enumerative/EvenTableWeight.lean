/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/EvenTableWeight.lean -/
module

public import Def.Combinatorics.Enumerative.EvenTableWeight
public import Def.MathlibExtTest.Combinatorics.Enumerative.EvenTableWeight
open scoped BigOperators

public section

namespace MetaMathlibExt

example : evenTableWeight testFactorFb63c6b5 testTableFb63c6b5 = 9 := rfl

example : evenTableWeight testFactorFb63c6b5 testTableFb63c6b5 =
    ∏ j, columnWeight 2 testFactorFb63c6b5
      (List.ofFn fun i => testTableFb63c6b5.entries i j) := rfl

end MetaMathlibExt
