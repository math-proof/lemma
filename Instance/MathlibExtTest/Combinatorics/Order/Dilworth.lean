module
public import Def.Combinatorics.Order.Dilworth
public import Theorem.Finset.Order.Dilworth
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Def.MathlibExtTest.Combinatorics.Order.Dilworth


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/Dilworth.lean -/
namespace MathlibExt.Combinatorics.Order.DilworthWanted

instance : Fintype Discrete3 := inferInstanceAs (Fintype (Fin 3))

instance : DecidableEq Discrete3 := inferInstanceAs (DecidableEq (Fin 3))

instance : PartialOrder Discrete3 where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

end MathlibExt.Combinatorics.Order.DilworthWanted
