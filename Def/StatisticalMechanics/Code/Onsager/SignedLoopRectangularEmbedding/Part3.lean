/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part2
open Set SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

def ons_rectDualDartDirection {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) : Fin 6 :=
  if dart.snd.1.val < dart.fst.1.val then 0
  else if dart.fst.1.val < dart.snd.1.val then 1
  else if dart.snd.2.val < dart.fst.2.val then 2 else 3


end
end StatMech.Onsager
