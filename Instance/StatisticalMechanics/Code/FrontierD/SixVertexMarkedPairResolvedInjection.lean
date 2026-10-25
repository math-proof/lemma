/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11


namespace StatMech.FrontierD

noncomputable section

instance instDecidablePropResolvedInjection (p : Prop) : Decidable p :=
  Classical.propDecidable p

instance instFintypeExplicitMarkedDecoratedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    Fintype (SixVertexExplicitMarkedDecoratedPair T left right k) :=
  Fintype.ofEquiv (SixVertexMarkedDecoratedPair T left right k)
    (sixVertexExplicitMarkedDecoratedPairEquiv T left right k).symm


end
end StatMech.FrontierD
