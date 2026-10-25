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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part122
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FreeQ2FixedInnerTwoSidedPositiveSubcritical := by
  intro β hβpos hβc
  rcases hdecay β hβpos hβc with ⟨Alo, AfkHi, mass, hmass, hbounds⟩
  exact ⟨Alo, AfkHi, mass, hmass,
    fkTwoSidedFreeIVQ2_of_freeFiniteVolumeBoundsOfBeta hβpos hbounds⟩


theorem
    freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_profile
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical) :
    FreeQ2FixedInnerProfileSameMassPositiveSubcritical := by
  intro β hβpos hβc
  rcases hfixed β hβpos hβc with ⟨Alo, AfkHi, mass, hmass, hconn⟩
  rcases hprofile β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨AprofHi, hprofileHi⟩
  exact ⟨Alo, AfkHi, AprofHi, mass, hmass, hconn, hprofileHi⟩


theorem freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_weak
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical) :
    FreeQ2FixedInnerProfileSameMassPositiveSubcritical :=
  freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_profile hfixed
    freeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical_trivial


theorem freeQ2BoundaryProfileForFixedInnerSameMass_of_subexponentialProfile
    (hprofile :
      FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
    FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass hmass hconn
  rcases hprofile β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨AprofHi, _hAprof, hprofileHi⟩
  exact ⟨AprofHi, hprofileHi⟩


end Exact3D
end StatMech
