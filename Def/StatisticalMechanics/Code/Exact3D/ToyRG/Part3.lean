/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Abbrev.StatisticalMechanics.Code.Exact3D.ToyRG.Part2


namespace StatMech

namespace Exact3D

noncomputable def toyHyperbolicRGMap (scale : BlockScale)
    (thermalEigenvalue stableEigenvalue : ℝ) :
    BlockSpinMap toyHyperbolicHamiltonianSpace where
  scale := scale
  map := fun x => (thermalEigenvalue * x.1, stableEigenvalue * x.2)


end Exact3D
end StatMech
