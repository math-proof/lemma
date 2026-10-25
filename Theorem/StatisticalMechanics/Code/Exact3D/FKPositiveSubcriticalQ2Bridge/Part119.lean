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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem freeQ2BoundaryVertexEpsilonRate_of_polynomialRateWithXAxisLogRate
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical := by
  intro β hβpos hβc
  rcases hrate β hβpos hβc with
    ⟨C, rate, k, hC, hpoint, hxAxisRate⟩
  refine ⟨rate, hxAxisRate, ?_⟩
  intro ε hε
  have hpref :
      ∀ᶠ n : ℕ in atTop,
        C * (n : ℝ) ^ k ≤ Real.exp (ε * (n : ℝ)) :=
    (PositiveSubexponentialPrefactor.const_mul hC
      (PositiveSubexponentialPrefactor.natCast_pow k)).eventually_le_exp_mul
        hε
  filter_upwards [hpoint, hpref] with n hpoint_n hpref_n
  intro v hv
  calc
    ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        ≤ C * (n : ℝ) ^ k * Real.exp (-(rate * (n : ℝ))) :=
      hpoint_n v hv
    _ ≤ Real.exp (ε * (n : ℝ)) * Real.exp (-(rate * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hpref_n (by positivity)
    _ = Real.exp (-((rate - ε) * (n : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring


theorem freeQ2BoundaryVertexEpsilonRate_of_directionalRate
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical :=
  freeQ2BoundaryVertexEpsilonRate_of_polynomialRateWithXAxisLogRate
    (freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
      hdir)


theorem freeQ2BoundaryVertexEpsilonRate_of_convexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical :=
  freeQ2BoundaryVertexEpsilonRate_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper
      htension)


theorem freeQ2BoundaryVertexEpsilonRate_of_actualConvexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical :=
  freeQ2BoundaryVertexEpsilonRate_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper
      htension)


theorem
    freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass _hmass hconn
  rcases hrate β hβpos hβc with
    ⟨C, rate, k, hC, hpoint, hxAxisRate⟩
  have hmass_eq_rate : mass = rate :=
    FKXAxisConnectionTwoSidedSubexponentialBounds.mass_eq_of_tendsto_neg_log_div
      hconn hxAxisRate
  refine ⟨C, rate, k, hC, ?_, hpoint⟩
  exact le_of_eq hmass_eq_rate


theorem freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass
    (hpoly :
      FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass hmass hconn
  rcases hpoly β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨C, boundaryMass, k, hC, hmass_le, hpoint⟩
  refine
    ⟨fun n : ℕ => C * (n : ℝ) ^ k,
      PositiveSubexponentialPrefactor.const_mul hC
        (PositiveSubexponentialPrefactor.natCast_pow k), ?_⟩
  filter_upwards [hpoint] with n hpoint_n
  intro v hv
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hmass_mul : mass * (n : ℝ) ≤ boundaryMass * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hmass_le hn_nonneg
  have hexp_le :
      Real.exp (-(boundaryMass * (n : ℝ))) ≤
        Real.exp (-(mass * (n : ℝ))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hpref_nonneg : 0 ≤ C * (n : ℝ) ^ k := by positivity
  calc
    ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        ≤ C * (n : ℝ) ^ k *
            Real.exp (-(boundaryMass * (n : ℝ))) :=
      hpoint_n v hv
    _ ≤ (C * (n : ℝ) ^ k) *
        Real.exp (-(mass * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp_le hpref_nonneg


theorem
    freeQ2BoundaryVertexPointwise_of_polynomialRateWithXAxisLogRate
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :=
  freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass
    (freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate
      hrate)


theorem freeQ2BoundaryVertexPointwise_of_directionalRate
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :=
  freeQ2BoundaryVertexPointwise_of_polynomialRateWithXAxisLogRate
    (freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
      hdir)


theorem freeQ2BoundaryVertexPointwise_of_convexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :=
  freeQ2BoundaryVertexPointwise_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper
      htension)


theorem freeQ2BoundaryVertexPointwise_of_actualConvexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :=
  freeQ2BoundaryVertexPointwise_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper
      htension)


theorem freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass hmass hconn
  rcases hprofile β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨Apoint, hApoint, hpoint⟩
  refine
    ⟨fun n =>
      ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * Apoint n,
      boxBoundaryCard3_mul_positiveSubexponentialPrefactor hApoint, ?_⟩
  have hprofileFromPoint :=
    eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_of_eventually_boundary
      hβpos hpoint
  filter_upwards [hprofileFromPoint] with n hprofile_n
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            (Apoint n * Real.exp (-(mass * (n : ℝ)))) :=
      hprofile_n
    _ =
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * Apoint n) *
          Real.exp (-(mass * (n : ℝ))) := by
      ring


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨Aratio, hAratio, hpoint⟩
  refine
    ⟨fun n =>
      ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * Aratio n,
      boxBoundaryCard3_mul_positiveSubexponentialPrefactor hAratio, ?_⟩
  have hprofile :=
    eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_of_eventually_boundary
      hβpos hpoint
  filter_upwards [hprofile] with n hprofile_n
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            (Aratio n *
              freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n) :=
      hprofile_n
    _ =
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * Aratio n) *
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n := by
      ring


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_polynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis
    (freeQ2BoundaryVertexSubexpComparisonToXAxis_of_polynomialComparison
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis
    (freeQ2BoundaryVertexSubexpComparisonToXAxis_of_finiteVolumeComparison
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumePolynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis
    (freeQ2BoundaryVertexFiniteVolumeComparisonToXAxis_of_finiteVolumePolynomial
      hcompare)


theorem freeQ2BoundaryProfileSubexpSameMass_of_subexpComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis
      hcompare)


theorem freeQ2BoundaryProfileSubexpSameMass_of_polynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_polynomialComparisonToXAxis
      hcompare)


theorem freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumeComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumePolynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumePolynomialComparisonToXAxis
      hcompare)


theorem freeQ2BoundaryProfileSubexpSameMass_of_envelopeAtLeastMass
    (henv :
      FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise
    (freeQ2BoundaryVertexPointwise_of_envelopeAtLeastMass henv)


theorem freeQ2BoundaryProfileSubexpSameMass_of_polynomialAtLeastMass
    (hpoly :
      FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise
    (freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass hpoly)


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_polynomialRateWithXAxisLogRate
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_polynomialAtLeastMass
    (freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate
      hrate)


theorem freeQ2BoundaryProfileSubexpSameMass_of_directionalRate
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_polynomialRateWithXAxisLogRate
    (freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
      hdir)


theorem freeQ2BoundaryProfileSubexpSameMass_of_convexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper
      htension)


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_actualConvexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper
      htension)


end Exact3D
end StatMech
