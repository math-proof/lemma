import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
open MeasureTheory SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkFiniteConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKFreeConnectionBoxEmbedding.lean)
-/
@[path]
private lemma fkFiniteConnectionEvent_isIncreasing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {source target : V} :
-- imply
  IsIncreasing (FKFiniteConnectionEvent G source target) := by
-- proof
  apply StatMech.FrontierD.fkFiniteConnectionEvent_isIncreasing G source target

/--
[fkFiniteConnection_reachable_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKFreeConnectionBoxEmbedding.lean)
-/
@[path]
private lemma fkFiniteConnection_reachable_box_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {N : Nat}
  {rho : ConfigSpace (Sym2 (FK.boxVerts 2 N))}
  {x y : V}
-- given
  (iota : V -> FK.boxVerts 2 N)
  (hadj : FK.ocd_AdjMatch G (FK.boxGraph 2 N) iota)
  (hreach : (FK.openSub G (FK.ocd_innerRestrict iota rho)).Reachable x y) :
-- imply
  (FK.openSub (FK.boxGraph 2 N) rho).Reachable (iota x) (iota y) := by
-- proof
  apply StatMech.FrontierD.fkFiniteConnection_reachable_box G N iota hadj rho hreach

/--
[fkFiniteConnection_cylinder_subset_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKFreeConnectionBoxEmbedding.lean)
-/
@[path]
private lemma fkFiniteConnection_cylinder_subset_boxConnEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {N : Nat}
  {source target : V}
-- given
  (iota : V -> FK.boxVerts 2 N)
  (hadj : FK.ocd_AdjMatch G (FK.boxGraph 2 N) iota) :
-- imply
  FK.boxRestrict 2 N ⁻¹' (FK.ocd_innerRestrict iota ⁻¹' FKFiniteConnectionEvent G source target) ⊆ FK.boxConnEvent 2 N (iota source) (iota target) := by
-- proof
  apply StatMech.FrontierD.fkFiniteConnection_cylinder_subset_boxConnEvent G N iota hadj source target

/--
[fkFiniteConnection_freeMass_le_boxConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKFreeConnectionBoxEmbedding.lean)
-/
@[path]
private lemma fkFiniteConnection_freeMass_le_boxConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {N : Nat}
  {source target : V}
  {p q : Real}
-- given
  (iota : V -> FK.boxVerts 2 N)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch G (FK.boxGraph 2 N) iota)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (∑ omega, (FKFiniteConnectionEvent G source target).indicator (fun _ => (1 : Real)) omega * FK.fkProb G p q omega) <= (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 N (iota source) (iota target)) := by
-- proof
  apply StatMech.FrontierD.fkFiniteConnection_freeMass_le_boxConn G N iota hiota hadj source target hp hp1 hq


-- created on 2026-10-23
