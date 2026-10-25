import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit.Part2
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[boxFinsetSpinSupport_map_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean)
-/
@[path]
private lemma boxFinsetSpinSupport_map_subtype_eq
  {d n : Nat}
  {A : Finset (Site d)}
-- given
  (hA : (↑A : Set (Site d)) ⊆ box d n) :
-- imply
  (boxFinsetSpinSupport d n A).map (Function.Embedding.subtype fun x ↦ x ∈ boxFinset d n) = A := by
-- proof
  apply StatMech.FrontierA.boxFinsetSpinSupport_map_subtype A hA

/--
[boxSpinSupport_map_iptp_boxEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean)
-/
@[path]
private lemma boxSpinSupport_map_iptp_boxEquiv_eq
  {d n : Nat}
  {A : Finset (Site d)} :
-- imply
  (boxSpinSupport d n A).map (iptp_boxEquiv d n).toEmbedding = boxFinsetSpinSupport d n A := by
-- proof
  apply StatMech.FrontierA.boxSpinSupport_map_iptp_boxEquiv A

/--
[isingExpectation_boxFinsetSpinSupport_eq_freeMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean)
-/
@[path]
private lemma isingExpectation_boxFinsetSpinSupport_eq_freeMeasure_eq
  {d n : Nat}
  {beta : Real}
  {A : Finset (Site d)}
-- given
  (hA : (↑A : Set (Site d)) ⊆ box d n) :
-- imply
  isingExpectation (graphS d (boxFinset d n)) beta 0 (spinProd (boxFinsetSpinSupport d n A)) = ∫ omega, spinProd A omega ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.isingExpectation_boxFinsetSpinSupport_eq_freeMeasure beta A hA

/--
[two_mul_succ_lt_isingDyadicSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean)
-/
@[path]
private lemma two_mul_succ_lt_isingDyadicSide_eq
  {n : Nat} :
-- imply
  2 * (n + 1) < isingDyadicSide n := by
-- proof
  apply StatMech.FrontierA.two_mul_succ_lt_isingDyadicSide n

/--
[criticalFreeState_eq_plusState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean)
-/
@[path]
private lemma criticalFreeState_eq_plusState_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  (freeState d (IsingFK.betaC (magnetization d)) 0 : Measure (ConfigSpace (Site d))) = (plusState d (IsingFK.betaC (magnetization d)) 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.criticalFreeState_eq_plusState hd

/--
[criticalTorusLocalSpinProd_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean)
-/
@[path]
private lemma criticalTorusLocalSpinProd_tendsto_eq
  {d : Nat}
  {A : Finset (Site d)}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (criticalTorusLocalSpinProd d A) atTop (nhds (∫ omega, spinProd A omega ∂(freeState d (IsingFK.betaC (magnetization d)) 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierA.criticalTorusLocalSpinProd_tendsto hd A


-- created on 2026-10-23
