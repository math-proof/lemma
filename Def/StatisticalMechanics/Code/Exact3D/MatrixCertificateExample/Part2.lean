/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

def stableCenterQ : Fin 2 → ℚ :=
  fun _ => 0


end MatrixCertificateExample
end Exact3D
end StatMech
