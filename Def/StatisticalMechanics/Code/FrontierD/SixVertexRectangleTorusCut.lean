/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
open Finset


namespace StatMech.FrontierD

def finLastOfPos {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (by omega)⟩

end StatMech.FrontierD
