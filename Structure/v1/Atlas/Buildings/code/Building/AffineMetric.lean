/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.AffineCoxeter.CanonicalMetric.Part2
import Lemma.Real.IsWInvariantEuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineMetric
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- A canonical metric on the realization of an affine Coxeter complex of
matrix $M$: a designated family of "chambers" $\{C\} \subseteq X$, each
bounded with diameter exactly $1$. -/
structure CanonicalMetric (M : CoxeterMatrix B) (X : Type*)
    [PseudoMetricSpace X] where
  chambers : Set (Set X)
  chamber_bounded : ∀ C ∈ chambers, Bornology.IsBounded C
  chamber_diam_one : ∀ C ∈ chambers, Metric.diam C = 1
  is_affine : M.IsAffine

