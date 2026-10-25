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
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- A map $f : X \to Y$ between pseudo-metric spaces is a similitude of
ratio $c > 0$ if $d(f(x), f(y)) = c \cdot d(x, y)$ for all $x, y \in X$. -/
def IsSimilitude {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (c : ℝ) : Prop :=
  0 < c ∧ ∀ x y : X, dist (f x) (f y) = c * dist x y

