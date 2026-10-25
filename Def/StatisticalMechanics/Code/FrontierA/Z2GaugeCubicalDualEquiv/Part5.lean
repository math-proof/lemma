/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part2
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

def cubicalDualEnds {a b c : Nat} :
    CubicalPlaquette a b c →
      CubicalDualVertex a b c × CubicalDualVertex a b c
  | .xy i j k =>
      ((finBackward k).map fun z => ⟨i, j, z⟩,
        (finForward k).map fun z => ⟨i, j, z⟩)
  | .xz i j k =>
      ((finBackward j).map fun y => ⟨i, y, k⟩,
        (finForward j).map fun y => ⟨i, y, k⟩)
  | .yz i j k =>
      ((finBackward i).map fun x => ⟨x, j, k⟩,
        (finForward i).map fun x => ⟨x, j, k⟩)


def cubicalPlaquetteCells {a b c : Nat} (p : CubicalPlaquette a b c) :
    Finset (CubicalCell a b c) :=
  (cubicalDualEnds p).1.toFinset ∪ (cubicalDualEnds p).2.toFinset

end
end StatMech.FrontierA
