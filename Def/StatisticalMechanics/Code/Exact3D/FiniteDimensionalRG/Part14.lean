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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part12


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

def scale : BlockScale where
  L := 2
  one_lt := by norm_num


noncomputable def model : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


noncomputable def certificate : RGCertificate model :=
  splitting.certificate scale model


end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
