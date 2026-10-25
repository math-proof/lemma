/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/Dilworth.lean -/


import Def.Combinatorics.Order.Dilworth
import Lemma.Finset.Order.Dilworth
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Defs.PartialOrder
import Def.MathlibExtTest.Combinatorics.Order.Dilworth


namespace MathlibExt.Combinatorics.Order.DilworthWanted

instance : Fintype Discrete3 := inferInstanceAs (Fintype (Fin 3))

instance : DecidableEq Discrete3 := inferInstanceAs (DecidableEq (Fin 3))

instance : PartialOrder Discrete3 where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

end MathlibExt.Combinatorics.Order.DilworthWanted
