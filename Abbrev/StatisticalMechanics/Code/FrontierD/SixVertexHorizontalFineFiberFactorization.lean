/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalBoundedSingleRowProfile (T : EvenTorus) :=
  Fin T.height -> Fin (T.width + 1) × Fin (T.width + 1)

end
end StatMech.FrontierD
