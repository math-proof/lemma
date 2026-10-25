/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def anisotropicSquareKWBlockPhase
    (L : Nat) (x y omega u v : Complex)
    (g : ZMod L × ZMod L) : Matrix (Fin 4) (Fin 4) Complex :=
  fun a b ↦ anisotropicSquareKWMatrixPhase L x y omega u v (g, a) (0, b)

end StatMech.FrontierA
