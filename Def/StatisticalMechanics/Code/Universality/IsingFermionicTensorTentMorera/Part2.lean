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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part3


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

noncomputable def axisMacroDirectContour
    (f : Complex -> Complex) (x y mesh : Real)
    (width height : Nat) : Complex :=
  (∑ k ∈ Finset.range width,
      complexDisplacementIntegral f
        ((x + (k : Real) * mesh : Real) + y * Complex.I) mesh) +
    (∑ k ∈ Finset.range height,
      complexDisplacementIntegral f
        ((x + (width : Real) * mesh : Real) +
          (y + (k : Real) * mesh : Real) * Complex.I)
        ((mesh : Complex) * Complex.I)) +
    (∑ k ∈ Finset.range width,
      complexDisplacementIntegral f
        ((x + (width : Real) * mesh + (k : Real) * (-mesh) : Real) +
          (y + (height : Real) * mesh : Real) * Complex.I)
        ((-mesh : Real) : Complex)) +
    ∑ k ∈ Finset.range height,
      complexDisplacementIntegral f
        (x + (y + (height : Real) * mesh +
          (k : Real) * (-mesh) : Real) * Complex.I)
        (((-mesh : Real) : Complex) * Complex.I)


noncomputable def axisTwoEdgeStaircasePathIntegral
    (f : Complex -> Complex) (x y mesh : Real)
    (width height : Nat) : Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (∑ k ∈ Finset.range width,
      let a : Complex :=
        (x + (k : Real) * mesh : Real) + y * Complex.I
      complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v) +
    (∑ k ∈ Finset.range height,
      let a : Complex :=
        (x + (width : Real) * mesh : Real) +
          (y + (k : Real) * mesh : Real) * Complex.I
      complexDisplacementIntegral f a v +
        complexDisplacementIntegral f (a + v) (-u)) +
    (∑ k ∈ Finset.range width,
      let a : Complex :=
        (x + (width : Real) * mesh - (k : Real) * mesh : Real) +
          (y + (height : Real) * mesh : Real) * Complex.I
      complexDisplacementIntegral f a (-u) +
        complexDisplacementIntegral f (a - u) (-v)) +
    ∑ k ∈ Finset.range height,
      let a : Complex :=
        x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
          Complex.I
      complexDisplacementIntegral f a (-v) +
        complexDisplacementIntegral f (a - v) u


end
end StatMech.Universality
