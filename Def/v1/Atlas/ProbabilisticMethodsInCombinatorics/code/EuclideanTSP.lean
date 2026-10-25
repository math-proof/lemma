/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/EuclideanTSP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.SpaceFillingCurve
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.SpaceFillingCurve
import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.EuclideanTSP
set_option maxHeartbeats 800000

open scoped Classical


namespace EuclideanTSP

variable {n : ℕ} [NeZero n]

/-- Length of the cyclic tour visiting the points $x$ in the order given by the
permutation $\sigma$: the sum of distances between consecutive points (mod $n$). -/
noncomputable def tourLength (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, dist (x (σ i)) (x (σ (i + 1)))

/-- Length of the shortest tour through the points $x$: the infimum of `tourLength x σ`
over all permutations $\sigma$. -/
noncomputable def shortestTour (x : Fin n → E2) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), tourLength x σ

/-- A point $p \in \mathbb{R}^2$ lies in the unit square $[0,1]^2$. -/
def InUnitSquare (p : E2) : Prop := ∀ j : Fin 2, 0 ≤ p j ∧ p j ≤ 1

/-- All points of the configuration $x$ lie in the unit square $[0,1]^2$. -/
def AllInUnitSquare (x : Fin n → E2) : Prop := ∀ i, InUnitSquare (x i)

/-- Certificate weights $\alpha_i$ in the Rhee–Talagrand TSP concentration argument:
twice the sum of the distances from $x_i$ to its successor and predecessor in the tour
$\sigma$. -/
noncomputable def cert (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  2 * (dist (x i) (x (σ (σ.symm i + 1))) + dist (x i) (x (σ (σ.symm i - 1))))

end EuclideanTSP
