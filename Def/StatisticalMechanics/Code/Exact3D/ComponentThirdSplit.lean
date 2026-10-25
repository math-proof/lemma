/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

noncomputable def boundaryVertexTanhNormalizedEmptyBoundaryTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  ((β * H) / Real.tanh (β * H)) *
    edgeCopySourcePairEmptyCollapsedSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})


noncomputable def boundaryVertexTanhNormalizedSimonDenominator
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  Sharpness.expectationJ G β
      (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n))) *
    edgeCopySourcePairEmptyCollapsedSum G β J
      (∅ : Finset (Option (FK.boxVerts 3 n)))


noncomputable def boundaryVertexTanhNormalizedOnePointTerm
    (β H : ℝ) (n : ℕ) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  (C / Real.tanh (β * H)) *
    edgeCopySourcePairSum G β J
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n)))


noncomputable def boundaryVertexTanhNormalizedBoundaryPairTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  (C / Real.tanh (β * H)) *
    edgeCopySourcePairSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})


noncomputable def boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  ((β * H) / Real.tanh (β * H)) *
    (Sharpness.currentSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
    Sharpness.currentSum G β J
      (∅ : Finset (Option (FK.boxVerts 3 n))))


noncomputable def boundaryVertexTanhNormalizedSimonCurrentDenominator
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  Sharpness.expectationJ G β
      (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n))) *
    (Sharpness.currentSum G β J
      (∅ : Finset (Option (FK.boxVerts 3 n))) *
    Sharpness.currentSum G β J
      (∅ : Finset (Option (FK.boxVerts 3 n))))


noncomputable def boundaryVertexTanhNormalizedOnePointCurrentTerm
    (β H : ℝ) (n : ℕ) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  (C / Real.tanh (β * H)) *
    (Sharpness.currentSum G β J (finiteBoundaryGhostOnePointSource 3 n) *
    Sharpness.currentSum G β J
      (∅ : Finset (Option (FK.boxVerts 3 n))))


noncomputable def boundaryVertexTanhNormalizedBoundaryPairCurrentTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  (C / Real.tanh (β * H)) *
    (Sharpness.currentSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
    Sharpness.currentSum G β J
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}))


noncomputable def boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  ((β * H) / Real.tanh (β * H)) *
    (Sharpness.currentSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) /
    Sharpness.currentSum G β J
      (∅ : Finset (Option (FK.boxVerts 3 n))))


noncomputable def boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    (β H : ℝ) (n : ℕ) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  (C / Real.tanh (β * H)) *
    (Sharpness.currentSum G β J (finiteBoundaryGhostOnePointSource 3 n) /
    Sharpness.currentSum G β J
      (∅ : Finset (Option (FK.boxVerts 3 n))))


noncomputable def boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  (C / Real.tanh (β * H)) *
    ((Sharpness.currentSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
    Sharpness.currentSum G β J
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})) /
    (Z0 * Z0))


noncomputable def boundaryVertexLocalizedSimonCurrentRatio
    (β H : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  Sharpness.expectationJ G β
    (Sharpness.couplingIn J (finiteBoundaryGhostOriginalSet 3 n))
    ({some (IsingFK.boxOrigin 3 n), some v} :
      Finset (Option (FK.boxVerts 3 n)))


noncomputable def boundaryVertexBoxSimonCurrentRatio
    (β : ℝ) (n : ℕ) (v : FK.boxVerts 3 n) : ℝ :=
  Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
    (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v})


end Exact3D
end StatMech
