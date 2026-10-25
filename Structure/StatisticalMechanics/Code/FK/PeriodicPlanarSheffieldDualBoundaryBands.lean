/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRecursiveLimits
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalBoundaryBandAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PairedAlignedMarginSchedule
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    (verticalRequirement horizontalRequirement : Nat → Nat) where
  horizontal : Nat → Nat
  vertical : Nat → Nat
  horizontal_tendsto : Tendsto horizontal atTop atTop
  vertical_tendsto : Tendsto vertical atTop atTop
  vertical_requirement : ∀ n,
    verticalRequirement (horizontal n) ≤ vertical n
  horizontal_requirement : ∀ n,
    horizontalRequirement (vertical n) ≤ horizontal (n + 1)
  primal_left_bottom : ∀ n,
    (family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 ≤
      family.baseBottom 1 + vertical n
  primal_right_bottom : ∀ n,
    (family.radiusRight (horizontal n) : Int) + family.baseRight 1 ≤
      family.baseBottom 1 + vertical n
  primal_left_top : ∀ n,
    (family.radiusLeft (horizontal n) : Int) + family.baseTop 1 ≤
      family.baseLeft 1 + vertical n
  primal_right_top : ∀ n,
    (family.radiusRight (horizontal n) : Int) + family.baseTop 1 ≤
      family.baseRight 1 + vertical n
  primal_bottom_left : ∀ n,
    (family.radiusBottom (vertical n) : Int) + family.baseBottom 0 ≤
      family.baseLeft 0 + horizontal (n + 1)
  primal_top_left : ∀ n,
    (family.radiusTop (vertical n) : Int) + family.baseTop 0 ≤
      family.baseLeft 0 + horizontal (n + 1)
  primal_bottom_right : ∀ n,
    (family.radiusBottom (vertical n) : Int) + family.baseRight 0 ≤
      family.baseBottom 0 + horizontal (n + 1)
  primal_top_right : ∀ n,
    (family.radiusTop (vertical n) : Int) + family.baseRight 0 ≤
      family.baseTop 0 + horizontal (n + 1)
  dual_left_bottom : ∀ n,
    (familyDual.radiusLeft (horizontal n) : Int) + familyDual.baseLeft 1 ≤
      familyDual.baseBottom 1 + vertical n
  dual_right_bottom : ∀ n,
    (familyDual.radiusRight (horizontal n) : Int) +
      familyDual.baseRight 1 ≤ familyDual.baseBottom 1 + vertical n
  dual_left_top : ∀ n,
    (familyDual.radiusLeft (horizontal n) : Int) + familyDual.baseTop 1 ≤
      familyDual.baseLeft 1 + vertical n
  dual_right_top : ∀ n,
    (familyDual.radiusRight (horizontal n) : Int) + familyDual.baseTop 1 ≤
      familyDual.baseRight 1 + vertical n
  dual_bottom_left : ∀ n,
    (familyDual.radiusBottom (vertical n) : Int) +
      familyDual.baseBottom 0 ≤ familyDual.baseLeft 0 + horizontal (n + 1)
  dual_top_left : ∀ n,
    (familyDual.radiusTop (vertical n) : Int) + familyDual.baseTop 0 ≤
      familyDual.baseLeft 0 + horizontal (n + 1)
  dual_bottom_right : ∀ n,
    (familyDual.radiusBottom (vertical n) : Int) +
      familyDual.baseRight 0 ≤ familyDual.baseBottom 0 + horizontal (n + 1)
  dual_top_right : ∀ n,
    (familyDual.radiusTop (vertical n) : Int) + familyDual.baseRight 0 ≤
      familyDual.baseTop 0 + horizontal (n + 1)

end StatMech.FK.PeriodicPlanar
