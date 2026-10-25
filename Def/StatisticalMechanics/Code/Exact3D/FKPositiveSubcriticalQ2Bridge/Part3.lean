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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part2
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def Q2PositiveSubcriticalNotBad : Prop :=
  ∀ β, 0 < β → β < Ising.betaC 3 →
    IsingFK.pOfBeta β ∉ FK.fwa_badP 3


def FreeFVQ2ExactPositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ A mass, 0 < A ∧ 0 < mass ∧
      FreeFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass


def WiredFVQ2ExactPositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ A mass, 0 < A ∧ 0 < mass ∧
      WiredFiniteVolumeQ2ExactExponentialOfBeta β hβpos A mass


def FreeFVQ2SubexpPositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (A : ℕ → ℝ) (mass : ℝ), 0 < mass ∧
      FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass


def WiredFVQ2SubexpPositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (A : ℕ → ℝ) (mass : ℝ), 0 < mass ∧
      WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta β hβpos A mass


def FreeFVQ2TwoSidedPositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (Alo Ahi : ℕ → ℝ) (mass : ℝ), 0 < mass ∧
      FreeFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass


def WiredFVQ2TwoSidedPositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (Alo Ahi : ℕ → ℝ) (mass : ℝ), 0 < mass ∧
      WiredFiniteVolumeQ2TwoSidedBoundsOfBeta β hβpos Alo Ahi mass


def FreeIsingThermodynamicLimitPositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    FreeIsingXAxisThermodynamicLimitToFiniteVolumes β


end Exact3D
end StatMech
