import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceCapstone
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.freeBufferedMeasure_real_cylinder_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma freeBufferedMeasure_real_cylinder_monotone_in_p_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {N m : Nat}
  {p₁ p₂ q : Real}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N ≤ m)
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hp₁₂ : p₁ ≤ p₂)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (P.freeBufferedMeasure m hp₁ hp₁' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤ (P.freeBufferedMeasure m hp₂ hp₂' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_real_cylinder_monotone_in_p P hNm hp₁ hp₁' hp₂ hp₂' hp₁₂ hq hS

/--
[PeriodicGraph.freeBufferedInfiniteVolume_real_cylinder_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_real_cylinder_monotone_in_p_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {N : Nat}
  {p₁ p₂ q : Real}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hp₁₂ : p₁ ≤ p₂)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (P.freeBufferedInfiniteVolume hp₁ hp₁' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤ (P.freeBufferedInfiniteVolume hp₂ hp₂' (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_real_cylinder_monotone_in_p P N hp₁ hp₁' hp₂ hp₂' hp₁₂ hq hS

/--
[PeriodicGraph.freeBufferedRootBoundaryCylinder_real_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma freeBufferedRootBoundaryCylinder_real_tendsto_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp₁ : p < 1)
  (hq : 0 < q) :
-- imply
  Tendsto (fun n => (P.freeBufferedInfiniteVolume hp hp₁ hq : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))) atTop (nhds (P.freeBufferedPercolationProbability p q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedRootBoundaryCylinder_real_tendsto P hp hp₁ hq

/--
[PeriodicGraph.freeBufferedPercolationProbability_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma freeBufferedPercolationProbability_monotoneOn_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  MonotoneOn (fun p => P.freeBufferedPercolationProbability p q) (Ioo (0 : Real) 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedPercolationProbability_monotoneOn P hq

/--
[PeriodicGraph.crossParameterWiredToFreeTransfer_of_monotonicity_agreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma crossParameterWiredToFreeTransfer_of_monotonicity_agreement_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hwired : MonotoneOn (fun p => P.wiredPercolationProbability p q) (Ioo (0 : Real) 1))
  (hfree : MonotoneOn (fun p => P.freeBufferedPercolationProbability p q) (Ioo (0 : Real) 1))
  (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
-- imply
  P.CrossParameterWiredToFreeTransfer q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.crossParameterWiredToFreeTransfer_of_monotonicity_agreement P hwired hfree hagrees

/--
[PeriodicGraph.crossParameterWiredToFreeTransfer_of_offCountableAgreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma crossParameterWiredToFreeTransfer_of_offCountableAgreement_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hagrees : P.FreeWiredPercolationAgreementOffCountable q) :
-- imply
  P.CrossParameterWiredToFreeTransfer q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.crossParameterWiredToFreeTransfer_of_offCountableAgreement P hq hagrees

/--
[PeriodicPlanarDualPair.freeCommonNoCoexistence_of_commonUniqueExclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma freeCommonNoCoexistence_of_commonUniqueExclusion_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 ≤ q)
  (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent = 0) :
-- imply
  D.FreeCommonNoCoexistence q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeCommonNoCoexistence_of_commonUniqueExclusion D hconn hconnDual hq hSheffield

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_freeCommon_and_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_freeCommon_and_transfer_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hcommon : D.FreeCommonNoCoexistence q)
  (htransfer : P.CrossParameterWiredToFreeTransfer q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_freeCommon_and_transfer D hq hcommon htransfer

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffield_and_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_sheffield_and_transfer_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 ≤ q)
  (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent = 0)
  (htransfer : P.CrossParameterWiredToFreeTransfer q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_sheffield_and_transfer D hconn hconnDual hq hSheffield htransfer

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_exponentialDecay_sheffield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean)
-/
@[path]
private lemma dualCritical_relation_of_exponentialDecay_sheffield_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hSheffield : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 V))) : Measure (ConfigSpace (Sym2 V))) D.commonUniqueInfiniteClusterEvent = 0)
  (htransfer : P.CrossParameterWiredToFreeTransfer q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_exponentialDecay_sheffield D H hconn hconnDual hpc hpcDual hq hdecay hSheffield htransfer


-- created on 2026-10-23
