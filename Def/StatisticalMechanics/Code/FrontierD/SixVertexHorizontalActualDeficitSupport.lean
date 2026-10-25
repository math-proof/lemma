/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalActualDeficitPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  token.2.1.1.1

def sixVertexHorizontalActualSurplusPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  token.2.1.1.1

end
end StatMech.FrontierD
