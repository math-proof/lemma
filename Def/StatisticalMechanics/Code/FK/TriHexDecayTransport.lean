/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


def SubcriticalTwoPointComparison
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Q : PeriodicGraph W)
    (q pcP pcQ : Real) : Prop :=
  ∀ p ∈ Ioo (0 : Real) pcQ,
    ∃ pP ∈ Ioo (0 : Real) pcP,
      ∃ K a b : Real, 0 < K ∧ 0 < a ∧ 0 ≤ b ∧
        ∃ f : W → V,
          (∀ x y : W,
            Q.wiredTwoPointProbability p q x y ≤
              K * P.wiredTwoPointProbability pP q (f x) (f y)) ∧
          (∀ x y : W,
            a * (Q.graph.dist x y : Real) ≤
              (P.graph.dist (f x) (f y) : Real) + b)


end PeriodicPlanar
end FK
end StatMech
