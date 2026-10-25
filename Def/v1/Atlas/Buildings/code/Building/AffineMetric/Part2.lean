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
import Structure.v1.Atlas.Buildings.code.Building.AffineMetric
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Classical
open ChamberComplex
open AffineCoxeter


/-- A canonical metric on $X$ is $W$-invariant under an action $W \times X
\to X$ if every $w \in W$ acts as an isometry on $X$. -/
def CanonicalMetric.IsWInvariant {M : CoxeterMatrix B} {X : Type*}
    [PseudoMetricSpace X]
    (_cm : CanonicalMetric M X)
    (action : M.Group → X → X) : Prop :=
  ∀ w : M.Group, ∀ x y : X, dist (action w x) (action w y) = dist x y

/-- The canonical distance on the Euclidean realization $E$ of an affine
Coxeter complex: $d(x, y) = \|x - y\| / \mathrm{diam}(C)$, where $C$ is
any chamber. This normalizes chambers to have diameter $1$. -/
noncomputable def CoxeterComplexCanonicalDist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : AffineCoxeterComplex E) (x y : E) : ℝ :=
  ‖x - y‖ / A.chamberDiameter

/-- The type of a per-apartment metric: a function assigning to each
apartment $A$ a (pseudo-)distance $V \times V \to \mathbb{R}$. -/
def apartmentMetric (b : Building V) :=
  { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments } → (V → V → ℝ)

