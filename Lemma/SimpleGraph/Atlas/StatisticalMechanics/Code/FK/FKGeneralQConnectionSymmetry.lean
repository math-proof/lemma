import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
open Filter Finset MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK


/--
[connProb_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionSymmetry.lean)
-/
@[path]
private lemma connProb_equiv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V ≃ V}
  {p q : Real}
  {x y : V}
-- given
  (hsigma : ∀ x y, G.Adj (sigma x) (sigma y) ↔ G.Adj x y) :
-- imply
  connProb G p q (sigma x) (sigma y) = connProb G p q x y := by
-- proof
  apply StatMech.FK.connProb_equiv G sigma hsigma p q x y

/--
[connProb_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionSymmetry.lean)
-/
@[path]
private lemma connProb_boxSym_eq
  {d : Nat}
  {S : BoxSym d}
  {n : Nat}
  {p q : Real}
  {x y : boxVerts d n} :
-- imply
  connProb (boxGraph d n) p q (S.lift n x) (S.lift n y) = connProb (boxGraph d n) p q x y := by
-- proof
  apply StatMech.FK.connProb_boxSym S n p q x y

/--
[fkgq_freeInfiniteVolume_connection_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConnectionSymmetry.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_connection_boxSym_eq
  {d : Nat}
  {S : BoxSym d}
  {p q : Real}
  {x y : Site d}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real {omega | StatMech.Lattice.Connected d omega (S.τ x) (S.τ y)} = (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real {omega | StatMech.Lattice.Connected d omega x y} := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_connection_boxSym hd S hp hp1 hq x y


-- created on 2026-10-23
