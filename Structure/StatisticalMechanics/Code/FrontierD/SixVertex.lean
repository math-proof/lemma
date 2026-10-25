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
open Finset Matrix


namespace StatMech.FrontierD

structure EvenTorus where
  width : ℕ
  height : ℕ
  width_pos : 0 < width
  height_pos : 0 < height
  width_even : Even width
  height_even : Even height


end StatMech.FrontierD
