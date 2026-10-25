/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


noncomputable def ons_turnMatrix (omega : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun nu mu => ons_turnW omega mu nu

end StatMech.Onsager
