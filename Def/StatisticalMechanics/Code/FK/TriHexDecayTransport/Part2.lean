/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexDecayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexDecayTransport
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


def TriHexGlobalTwoPointComparison (q pcTri pcHex : Real) : Prop :=
  SubcriticalTwoPointComparison triangular hexagonal q pcTri pcHex


def TriHexGlobalProbabilityComparison (q pcTri pcHex : Real) : Prop :=
  ∀ p ∈ Ioo (0 : Real) pcHex,
    ∃ pTri ∈ Ioo (0 : Real) pcTri,
      ∃ K : Real, 0 < K ∧
        ∀ u v : HexVertex,
          hexagonal.wiredTwoPointProbability p q u v ≤
            K * triangular.wiredTwoPointProbability pTri q
              (hexToTriAnchor u) (hexToTriAnchor v)


end PeriodicPlanar
end FK
end StatMech
