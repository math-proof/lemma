import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkSquareBoxPlanar_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDuality.lean)
-/
@[path]
private lemma fkSquareBoxPlanar_graph_eq
  {n : Nat} :
-- imply
  (fkSquareBoxPlanar n).G = FK.boxGraph 2 n := by
-- proof
  apply StatMech.FrontierD.fkSquareBoxPlanar_graph n

/--
[fkSquareBoxPlanar_emb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDuality.lean)
-/
@[path]
private lemma fkSquareBoxPlanar_emb_eq
  {n : Nat}
  {x : FK.boxVerts 2 n} :
-- imply
  (fkSquareBoxPlanar n).emb x = (x : Site 2) := by
-- proof
  apply StatMech.FrontierD.fkSquareBoxPlanar_emb n x

/--
[fkSquareBox_fkWeight_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDuality.lean)
-/
@[path]
private lemma fkSquareBox_fkWeight_duality_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkWeight (FK.boxGraph 2 n) p q omega * q ^ ((FK.boxGraph 2 n).edgeFinset.card + 1) = (p / (1 - dualParam p q)) ^ (FK.boxGraph 2 n).edgeFinset.card * q ^ Nat.card (FK.boxVerts 2 n) * pfdDualWeight (fkSquareBoxPlanar n) (dualParam p q) q (FK.openSub (FK.boxGraph 2 n) omega) := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_fkWeight_duality n omega hp hp1 hq

/--
[fkSquareBox_fkProb_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDuality.lean)
-/
@[path]
private lemma fkSquareBox_fkProb_duality_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkProb (FK.boxGraph 2 n) p q omega = pfdDualProb (fkSquareBoxPlanar n) (dualParam p q) q omega := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_fkProb_duality n omega hp hp1 hq

/--
[fkSquareBox_fkProb_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDuality.lean)
-/
@[path]
private lemma fkSquareBox_fkProb_selfDual_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.fkProb (FK.boxGraph 2 n) (selfDualPoint q) q omega = pfdDualProb (fkSquareBoxPlanar n) (selfDualPoint q) q omega := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_fkProb_selfDual n omega hq


-- created on 2026-10-23
