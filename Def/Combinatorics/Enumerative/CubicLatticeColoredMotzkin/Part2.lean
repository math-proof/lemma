module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
public import Lemma.Finset.Enumerative.ULDMotzkinNumberOfRankR
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Theorem.Combinatorics.Enumerative.CubicLatticeColoredMotzkin


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean -/
namespace MetaMathlibExt

/-- Forward step map of the label bijection. -/
def cubeToMotzkinStep (n : ℕ) (x : Fin (n + 1) × Bool) :
    Sum Bool (Fin (2 * n)) :=
  if h : x.1 = Fin.last n then Sum.inl x.2 else Sum.inr (flatIndex n x h)

/-- Backward step map. -/
def motzkinToCubeStep (n : ℕ) (y : Sum Bool (Fin (2 * n))) :
    Fin (n + 1) × Bool :=
  Sum.elim (fun b => (Fin.last n, b)) (fun j =>
    (⟨j.val / 2, by
      have hj := j.isLt
      omega⟩, decide (j.val % 2 = 1))) y

end MetaMathlibExt
