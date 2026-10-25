/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/Dilworth.lean -/


import Def.Combinatorics.Order.Dilworth
import Lemma.Finset.Order.Dilworth
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Defs.PartialOrder
import Theorem.MathlibExtTest.Combinatorics.Order.Dilworth


namespace MathlibExt.Combinatorics.Order.DilworthWanted

/-- `Fin 3` with the discrete order: distinct elements are incomparable. -/
def Discrete3 := Fin 3

end MathlibExt.Combinatorics.Order.DilworthWanted
