/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part92
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let C := (β * H) * (β * H)
  let onePoint :=
    C * edgeCopySourcePairSum G β J
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n)))
  let boundaryPair := fun v : FK.boxVerts 3 n =>
    C * edgeCopySourcePairSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
  let emptyBoundary := fun v : FK.boxVerts 3 n =>
    (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  (I.image.card : ℝ) *
      (onePoint + ∑ v ∈ B, boundaryPair v) +
    ∑ v ∈ B, emptyBoundary v


noncomputable def finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  let onePoint :=
    (C / T) * edgeCopySourcePairSum G β J
      (finiteBoundaryGhostOnePointSource 3 n)
      (∅ : Finset (Option (FK.boxVerts 3 n)))
  let boundaryPair := fun v : FK.boxVerts 3 n =>
    (C / T) * edgeCopySourcePairSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
      (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})
  let emptyBoundary := fun v : FK.boxVerts 3 n =>
    ((β * H) / T) * edgeCopySourcePairEmptyCollapsedSum G β J
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  (I.image.card : ℝ) *
      (onePoint + ∑ v ∈ B, boundaryPair v) +
    ∑ v ∈ B, emptyBoundary v


noncomputable def
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  let onePoint :=
    (C / T) *
      (Sharpness.currentSum G β J (finiteBoundaryGhostOnePointSource 3 n) *
        Sharpness.currentSum G β J (∅ : Finset (Option (FK.boxVerts 3 n))))
  let boundaryPair := fun v : FK.boxVerts 3 n =>
    (C / T) *
      (Sharpness.currentSum G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
        Sharpness.currentSum G β J
          (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}))
  let emptyBoundary := fun v : FK.boxVerts 3 n =>
    ((β * H) / T) *
      (Sharpness.currentSum G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
        Sharpness.currentSum G β J (∅ : Finset (Option (FK.boxVerts 3 n))))
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  (I.image.card : ℝ) *
      (onePoint + ∑ v ∈ B, boundaryPair v) +
    ∑ v ∈ B, emptyBoundary v


noncomputable def
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  (I.image.card : ℝ) *
    ((C / T) *
      (Sharpness.currentSum G β J (finiteBoundaryGhostOnePointSource 3 n) *
        Sharpness.currentSum G β J (∅ : Finset (Option (FK.boxVerts 3 n)))))


noncomputable def
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let C := (β * H) * (β * H)
  let boundaryPair := fun v : FK.boxVerts 3 n =>
    (C / T) *
      (Sharpness.currentSum G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
        Sharpness.currentSum G β J
          (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}))
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  (I.image.card : ℝ) * ∑ v ∈ B, boundaryPair v


noncomputable def
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) : ℝ :=
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let T := Real.tanh (β * H)
  let emptyBoundary := fun v : FK.boxVerts 3 n =>
    ((β * H) / T) *
      (Sharpness.currentSum G β J
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
        Sharpness.currentSum G β J (∅ : Finset (Option (FK.boxVerts 3 n))))
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  ∑ v ∈ B, emptyBoundary v


end Exact3D
end StatMech
