/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

structure IntegralSquareTorusCycle (L : Nat) [NeZero L] where
  horizontal : (ZMod L × ZMod L) → Int
  vertical : (ZMod L × ZMod L) → Int
  divergence_zero : ∀ p,
    horizontal p + vertical p -
      horizontal (p.1 - 1, p.2) -
      vertical (p.1, p.2 - 1) = 0

end
end StatMech.FrontierD
