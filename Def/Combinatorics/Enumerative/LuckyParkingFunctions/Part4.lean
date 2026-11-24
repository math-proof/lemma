module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Instance.Combinatorics.Enumerative.LuckyParkingFunctions.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

def fiberToProd (n : ℕ) (i0 : Fin n) (x : Fiber n i0) :
    Park i0.val × Park (n - i0.val) :=
  (⟨splitLower n x.1.1 x.1.2 i0, splitLower_mono n x.1.1 x.1.2 i0,
      fun j => splitLower_bound n x.1.1 x.1.2 i0 j⟩,
    ⟨splitUpper n x.1.1 x.1.2 i0 x.2,
      splitUpper_mono n x.1.1 x.1.2 i0 x.2,
      fun k => splitUpper_bound n x.1.1 x.1.2 i0 x.2 k⟩)

def fiberFromProd (n : ℕ) (i0 : Fin n)
    (p : Park i0.val × Park (n - i0.val)) : Fiber n i0 :=
  ⟨⟨joinFun n i0 p.1 p.2, joinFun_mono n i0 p.1 p.2,
      fun j => joinFun_bound n i0 p.1 p.2 j⟩,
    joinFun_fixed n i0 p.1 p.2⟩

end MetaMathlibExt
end
