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
import Abbrev.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part2


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

noncomputable def rgMap {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) : BlockSpinMap H.hamiltonian where
  scale := scale
  map := H.step


noncomputable def fixedPointData {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) : RGFixedPointData H.hamiltonian (H.rgMap scale) where
  fixedPoint := origin
  fixedPoint_eq := H.step_origin
  thermalEigenvalue := H.thermal
  thermal_gt_one := H.thermal_gt_one


noncomputable def certificate {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) : RGCertificate M where
  H := H.hamiltonian
  R := H.rgMap scale
  fixedPointData := H.fixedPointData scale

end FiniteHyperbolicSplitting
end Exact3D
end StatMech
