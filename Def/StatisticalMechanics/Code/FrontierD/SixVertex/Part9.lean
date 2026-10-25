/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Hom.PowersetCard
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertex.Part7
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def sixVertexLambda (N r : ℕ) (_hN : Even N) (_hr : r ≤ N / 2)
    (c : ℝ) : ℝ :=
  sixVertexSectorTopEigenvalue N (N / 2 - r)
    ((Nat.sub_le _ _).trans (Nat.div_le_self N 2)) c

end StatMech.FrontierD
