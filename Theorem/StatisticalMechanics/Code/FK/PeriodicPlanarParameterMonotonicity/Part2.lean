/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarParameterMonotonicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalAssembly
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

section Countable

variable [Countable V]


theorem PeriodicGraph.wiredPercolationProbability_monotoneOn_of_cylinderApproximation
    (P : PeriodicGraph V) {q : Real} (hq : 1 <= q)
    (happrox : P.HasPercolationCylinderApproximation q) :
    MonotoneOn (fun p => P.wiredPercolationProbability p q)
      (Ioo (0 : Real) 1) := by
  rintro p1 hp1 p2 hp2 hp12
  obtain ⟨A, hA, hlim⟩ := happrox
  apply le_of_tendsto_of_tendsto
    (hlim p1 hp1.1 hp1.2 hq) (hlim p2 hp2.1 hp2.2 hq)
  exact Filter.Eventually.of_forall fun n =>
    P.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p n
      hp1.1 hp1.2 hp2.1 hp2.2 hp12 hq (hA n)

end Countable


theorem PeriodicGraph.dualCritical_relation_of_cylinderApproximation_noCoexistence
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 1 <= q)
    (happrox : P.HasPercolationCylinderApproximation q)
    (happroxDual : Pdual.HasPercolationCylinderApproximation q)
    (hcoverage : DualSubcriticalCoverage
      (fun p => Pdual.wiredPercolates p q) (P.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q) :
    BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply P.dualCritical_relation_of_monotonicity_noCoexistence Pdual
    hpc hpcDual (zero_lt_one.trans_le hq)
  · exact P.wiredPercolationProbability_monotoneOn_of_cylinderApproximation hq happrox
  · exact Pdual.wiredPercolationProbability_monotoneOn_of_cylinderApproximation
      hq happroxDual
  · exact hcoverage
  · exact hnoCoexistence

end StatMech.FK.PeriodicPlanar
