module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
public import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Abbrev.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable instance PeriodicPlaneEmbedding.instFintypeRectVertex
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Fintype (E.RectVertex a b c d) :=
  (E.rectVertices_finite a b c d).fintype

instance PeriodicPlaneEmbedding.instDecidableEqRectVertex
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    DecidableEq (E.RectVertex a b c d) := Subtype.instDecidableEq


end StatMech.FK.PeriodicPlanar
