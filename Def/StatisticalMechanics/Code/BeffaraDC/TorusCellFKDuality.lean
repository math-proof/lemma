/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part6
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusCellPrimalWeight (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (K : SimpleGraph (ZMod L × ZMod L)) : ℝ :=
  edgeProductCount p (onsTorusGraph L).edgeFinset.card K.edgeSet.ncard *
    q ^ Nat.card K.ConnectedComponent


noncomputable def torusCellDualWeight (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (K : SimpleGraph (ZMod L × ZMod L)) : ℝ :=
  edgeProductCount p (onsTorusGraph L).edgeFinset.card
      ((onsTorusGraph L).edgeFinset.card - K.edgeSet.ncard) *
    q ^ torusCellFaceCount L K


end StatMech.BeffaraDC
