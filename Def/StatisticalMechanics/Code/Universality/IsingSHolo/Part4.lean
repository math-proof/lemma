/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Universality.IsingSHolo


namespace StatMech.Universality

open Complex


namespace IsingMedialVertex

variable (D : IsingMedialVertex)


noncomputable def edgeObs (k : Fin 4) : ℂ := isingF k D.X


end IsingMedialVertex
end StatMech.Universality
