/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part8


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialAxisStaircaseBoundaryIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat) : Complex :=
  (∑ k ∈ Finset.range width,
      (reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + height + k) (j0 + k) +
        reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + height + k + 1) (j0 + k))) +
    (∑ k ∈ Finset.range height,
      (reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + width + (height - 1 - k) + 1) (j0 + width + k) -
        reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + width + (height - 1 - k)) (j0 + width + k + 1))) +
    (∑ k ∈ Finset.range width,
      (-reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k) + 1) -
        reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + (width - 1 - k))
          (j0 + height + (width - 1 - k)))) +
    ∑ k ∈ Finset.range height,
      (-reflectedRadialVerticalEdgeIntegral mesh F
          (i0 + k) (j0 + (height - 1 - k)) +
        reflectedRadialHorizontalEdgeIntegral mesh F
          (i0 + k) (j0 + (height - 1 - k)))


noncomputable def reflectedRadialAxisStaircasePathIntegral
    (f : Complex -> Complex) (mesh : Real) (n i0 j0 width height : Nat) :
    Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (∑ k ∈ Finset.range width,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            mesh n (i0 + height + k) (j0 + k)) u +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition
            mesh n (i0 + height + k + 1) (j0 + k)) v)) +
    (∑ k ∈ Finset.range height,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + width + (height - 1 - k) + 1) (j0 + width + k)) v +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + width + (height - 1 - k) + 1)
            (j0 + width + k + 1)) (-u))) +
    (∑ k ∈ Finset.range width,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + (width - 1 - k) + 1)
            (j0 + height + (width - 1 - k) + 1)) (-u) +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + (width - 1 - k))
            (j0 + height + (width - 1 - k) + 1)) (-v))) +
    ∑ k ∈ Finset.range height,
      (complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + k) (j0 + (height - 1 - k) + 1)) (-v) +
        complexDisplacementIntegral f
          (isingReflectedCenteredRadialGridPosition mesh n
            (i0 + k) (j0 + (height - 1 - k))) u)


end
end StatMech.Universality
