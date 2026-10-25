/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Real.Cardinality
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualBurtonKeane.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictCriticalAssembly
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def PeriodicGraph.freeBufferedPercolationProbability
    (P : PeriodicGraph V) (p q : Real) : Real :=
  if h : p ∈ Ioo (0 : Real) 1 ∧ 0 < q then
    ((P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real P.percolationEvent
  else 0


def PeriodicGraph.FreeBufferedPercolates
    (P : PeriodicGraph V) (p q : Real) : Prop :=
  0 < P.freeBufferedPercolationProbability p q


def PeriodicPlanarDualPair.FreeCommonNoCoexistence
    (D : PeriodicPlanarDualPair P Pdual) (q : Real) : Prop :=
  ∀ p ∈ Ioo (0 : Real) 1,
    ¬ (P.FreeBufferedPercolates p q ∧ D.FreeDualPercolates p q)


def PeriodicGraph.CrossParameterWiredToFreeTransfer
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∀ r ∈ Ioo (0 : Real) 1, ∀ p ∈ Ioo (0 : Real) 1, r < p ->
    P.wiredPercolates r q -> P.FreeBufferedPercolates p q


def PeriodicGraph.FreeWiredPercolationAgreementOffCountable
    (P : PeriodicGraph V) (q : Real) : Prop :=
  ∃ exceptional : Set Real, exceptional.Countable ∧
    ∀ p ∈ Ioo (0 : Real) 1, p ∉ exceptional ->
      P.freeBufferedPercolationProbability p q =
        P.wiredPercolationProbability p q


end StatMech.FK.PeriodicPlanar
