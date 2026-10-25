/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Abbrev.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

def origin {n : ℕ} : State n :=
  (0, 0)


noncomputable def step {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (x : State n) : State n :=
  (H.thermal * x.1, H.stable.step x.2)


noncomputable def iterate {n : ℕ} (H : FiniteHyperbolicSplitting n) :
    ℕ → State n → State n
  | 0, x => x
  | k + 1, x => H.step (H.iterate k x)


end FiniteHyperbolicSplitting
end Exact3D
end StatMech
