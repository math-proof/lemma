/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part7
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure AlignedCrossNestedPairedSequence
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n))
    (padding : Nat) where
  radius : Nat -> Nat
  schedule : forall n, PairedAlignedMarginSchedule E Edual
    (family n) (familyDual n) (fun _ => 0) (fun _ => 0)
  index : Nat -> Nat
  slack : forall n, PairedAlignedConnectorSlack E Edual
    (family n) (familyDual n) (schedule n) (max (radius n) n) (index n)
  triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
    E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n)
    (family n) (familyDual n) (schedule n) (index n) padding


end StatMech.FK.PeriodicPlanar
