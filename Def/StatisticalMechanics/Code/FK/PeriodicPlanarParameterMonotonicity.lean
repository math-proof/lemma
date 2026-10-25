/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarParameterMonotonicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalAssembly
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

section Countable

variable [Countable V]


def PeriodicGraph.HasPercolationCylinderApproximation
    (P : PeriodicGraph V) (q : Real) : Prop :=
  exists A : forall n : Nat,
      Set (ConfigSpace (Sym2 (P.BufferedVertex n))),
    (forall n, IsIncreasing (A n)) /\
      forall p (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q),
        Tendsto
          (fun n =>
            (P.wiredBufferedInfiniteVolume hp hp1
                (zero_lt_one.trans_le hq) :
              Measure (ConfigSpace (Sym2 V))).real
              (P.bufferedCylinder n (A n)))
          atTop (nhds (P.wiredPercolationProbability p q))


end Countable
end StatMech.FK.PeriodicPlanar
