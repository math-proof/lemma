/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianAtlas
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {V E D Component : Type*}
  [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  [Fintype Component] [DecidableEq Component]


structure IsoradialMetricComponentOrientationData
    (Component : Type*) [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFOutgoingConductance conductance next =
      ∏ edge ∈ outgoingEdgeSet next, weight edge
  supported : Finset E -> Prop
  components : Finset E -> Finset Component
  componentHolonomy : Finset E -> Component -> Complex
  boundaryCoefficient_supported : forall (F : Finset E), supported F ->
    ribbonBoundaryCharacterCoefficient R character F =
      ∏ component : {component // component ∈ components F},
        formanCycleCoefficient (componentHolonomy F component)
  boundaryCoefficient_unsupported : forall (F : Finset E), ¬ supported F ->
    ribbonBoundaryCharacterCoefficient R character F = 0
  fiberEmpty_unsupported : forall (F : Finset E), ¬ supported F ->
    IsEmpty (finiteMapFiber outgoingEdgeSet F)
  orientationOf : forall (F : Finset E) (_hF : supported F),
    finiteMapFiber outgoingEdgeSet F ->
      ({component // component ∈ components F} -> Bool)
  outgoingOfOrientation : forall (F : Finset E) (_hF : supported F),
    ({component // component ∈ components F} -> Bool) ->
      finiteMapFiber outgoingEdgeSet F
  outgoingOf_orientationOf : forall (F : Finset E) (hF : supported F)
      (next : finiteMapFiber outgoingEdgeSet F),
    outgoingOfOrientation F hF (orientationOf F hF next) = next
  orientationOf_outgoingOf : forall (F : Finset E) (hF : supported F)
      (orientation : {component // component ∈ components F} -> Bool),
    orientationOf F hF (outgoingOfOrientation F hF orientation) = orientation
  formanFactor_orientation : forall (F : Finset E) (hF : supported F)
      (next : finiteMapFiber outgoingEdgeSet F),
    (∏ cycle : finiteCRSFAtomicCycle next.1,
      (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)) =
      ∏ component : {component // component ∈ components F},
        if orientationOf F hF next component then
          1 - componentHolonomy F component
        else 1 - (componentHolonomy F component)⁻¹

end StatMech.FrontierA
