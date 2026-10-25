/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part12
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskTransferOrbitInternallyComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r c : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r c ->
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1


def CanonicalMaskAdjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r x y : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
      CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ->
        CanonicalTransferWorks ends m k zero r.1.1 y.1.1


def CanonicalMaskOrbitCoverageMaximal
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r : leftMaskFiber ends m j k l zero p) : Prop :=
  ∀ t : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r t ->
      (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
        (canonicalMaskOrbitCoverage ends m j k l zero p r).card


def CanonicalMaskAdjacentCoverageBoundary
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r x y : leftMaskFiber ends m j k l zero p) : Prop :=
  CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
    CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
    CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
    ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1


def CanonicalMaskAdjacentNormalInvariant
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ x y : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
      canonicalNormalRow ends m k zero x.1.1 =
        canonicalNormalRow ends m k zero y.1.1


def CanonicalMaskNormalFiberComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r c : leftMaskFiber ends m j k l zero p,
    canonicalNormalRow ends m k zero r.1.1 =
        canonicalNormalRow ends m k zero c.1.1 ->
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1


end StatMech.GrahamGHS.FourColor
