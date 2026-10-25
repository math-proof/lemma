/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part4


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_zmodPrefix
    {A : Type*} [AddCommMonoid A]
    {L : ℕ} [NeZero L] (f : ZMod L → A) (z : ZMod L) : A :=
  ∑ i ∈ Finset.range z.val, f ((i + 1 : ℕ) : ZMod L)

end StatMech.Onsager
