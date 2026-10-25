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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part8


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

noncomputable def exactScaleObservable {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) : ℝ → ℝ :=
  fun β : ℝ =>
    Real.exp (-(H.certificate scale M).predictedExponent *
      Real.log (M.betaC - β))

end FiniteHyperbolicSplitting
end Exact3D
end StatMech
