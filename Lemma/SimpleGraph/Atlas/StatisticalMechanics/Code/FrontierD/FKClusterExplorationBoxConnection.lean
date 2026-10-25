import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKClusterExplorationBoxConnection
open MeasureTheory SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkClusterExploration_condConnectionMass_le_boxConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKClusterExplorationBoxConnection.lean)
-/
@[path]
private lemma fkClusterExploration_condConnectionMass_le_boxConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {rho : ConfigSpace (Sym2 V)}
  {roots : Finset V}
  {N : Nat}
  {source target : FK.ClusterUnexploredVertex G rho roots}
  {p q : Real}
-- given
  (iota : FK.ClusterUnexploredVertex G rho roots -> FK.boxVerts 2 N)
  (hiota : Function.Injective iota)
  (hadj : FK.ocd_AdjMatch (FK.clusterUnexploredGraph G rho roots) (FK.boxGraph 2 N) iota)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (∑ sigma : ConfigSpace (Sym2 V), (FK.ocd_innerRestrict (Subtype.val : FK.ClusterUnexploredVertex G rho roots -> V) ⁻¹' FKFiniteConnectionEvent (FK.clusterUnexploredGraph G rho roots) source target).indicator (fun _ => (1 : Real)) sigma * FK.condBcProb G (StatMech.Lattice.boundaryCliqueGraph (FK.clusterNoBoundary : V -> Prop)) p q (FK.clusterUnexploredPairEdges G rho roots) rho sigma) <= (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 N (iota source) (iota target)) := by
-- proof
  apply StatMech.FrontierD.fkClusterExploration_condConnectionMass_le_boxConn G rho roots N iota hiota hadj source target hp hp1 hq


-- created on 2026-10-23
