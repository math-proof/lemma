/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/Dilworth.lean -/

module

public import Def.Combinatorics.Order.Dilworth
public import Theorem.Finset.Order.Dilworth
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Theorem.MathlibExtTest.Combinatorics.Order.Dilworth

@[expose] public section

namespace MathlibExt.Combinatorics.Order.DilworthWanted

/-- `Fin 3` with the discrete order: distinct elements are incomparable. -/
def Discrete3 := Fin 3

end MathlibExt.Combinatorics.Order.DilworthWanted
