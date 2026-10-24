import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
open MeasureTheory SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkRectPrimalUnexploredConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalPairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {source target : FKRectPrimalUnexploredVertex R S eta} :
-- imply
  IsIncreasing (FKRectPrimalUnexploredConnectionEvent R S eta source target) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredConnectionEvent_isIncreasing R S eta source target

/--
[fkRectPrimalUnexplored_connectionCylinder_subset_boxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalPairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_connectionCylinder_subset_boxConnEvent_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {source target : FKRectPrimalUnexploredVertex R S eta} :
-- imply
  FK.boxRestrict 2 (R.width + R.height) ⁻¹' (FK.ocd_innerRestrict (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' FKRectPrimalUnexploredConnectionEvent R S eta source target) ⊆ FK.boxConnEvent 2 (R.width + R.height) (fkRectPrimalUnexploredBoxEmbedding R S eta source) (fkRectPrimalUnexploredBoxEmbedding R S eta target) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_connectionCylinder_subset_boxConnEvent R S eta source target

/--
[fkRectPrimalUnexploredConnection_freeMass_le_boxConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalPairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredConnection_freeMass_le_boxConn_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {source target : FKRectPrimalUnexploredVertex R S eta}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (∑ omega, (FKRectPrimalUnexploredConnectionEvent R S eta source target).indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega) <= (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 (R.width + R.height) (fkRectPrimalUnexploredBoxEmbedding R S eta source) (fkRectPrimalUnexploredBoxEmbedding R S eta target)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredConnection_freeMass_le_boxConn R S eta source target hp hp1 hq


-- created on 2026-10-23
