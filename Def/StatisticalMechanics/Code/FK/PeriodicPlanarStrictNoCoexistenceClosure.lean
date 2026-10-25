/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceCapstone
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def PeriodicGraph.freeBufferedBoundaryCylinderProbability
    (P : PeriodicGraph V) (n : Nat) (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))
  else 0


noncomputable def PeriodicGraph.wiredBufferedBoundaryCylinderProbability
    (P : PeriodicGraph V) (n : Nat) (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))
  else 0


noncomputable def PeriodicGraph.freeBufferedCylinderProbability
    (P : PeriodicGraph V) (n : Nat)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))))
    (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n S)
  else 0


noncomputable def PeriodicGraph.wiredBufferedCylinderProbability
    (P : PeriodicGraph V) (n : Nat)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))))
    (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    (P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder n S)
  else 0


def PeriodicGraph.FreeWiredIncreasingCylinderAgreementOffCountable
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∀ n : Nat,
    {p : Real | ∃ S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))),
      IsIncreasing S ∧
        P.freeBufferedCylinderProbability n S p q ≠
          P.wiredBufferedCylinderProbability n S p q}.Countable


def PeriodicGraph.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∀ n : Nat,
    {t : Real | ∃ S : Set (ConfigSpace (Sym2 (P.BufferedVertex n))),
      IsIncreasing S ∧
        P.freeBufferedCylinderProbability n S (fsc_logistic t) q ≠
          P.wiredBufferedCylinderProbability n S (fsc_logistic t) q}.Countable


end StatMech.FK.PeriodicPlanar
