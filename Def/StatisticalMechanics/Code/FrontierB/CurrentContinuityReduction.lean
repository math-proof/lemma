/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfinitePlusFreeSourceSwitching
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.Sharpness.IsingMagnetizationZero
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
open Filter MeasureTheory Set Topology BoundedContinuousFunction


namespace StatMech.FrontierB

open Ising Lattice Percolation Sharpness

variable {d : ℕ}


noncomputable def currentContinuityMixedTraceLaw
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  independentSuperposedTraceLaw
    (infinitePlusCurrentMeasure d beta hbeta.le)
    (infiniteFreeCurrentMeasure d beta hbeta.le)


noncomputable def currentContinuityFreeTwoPoint
    (d : ℕ) (beta : ℝ) (x y : Site d) : ℝ :=
  ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
    ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))


noncomputable def currentContinuityPlusTwoPoint
    (d : ℕ) (beta : ℝ) (x y : Site d) : ℝ :=
  ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
    ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))


def CurrentContinuityFreeLROZero (d : ℕ) (beta : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℕ, ∀ x : Site d,
    x ∉ box d R →
      |currentContinuityFreeTwoPoint d beta (Percolation.origin d) x| < epsilon


def CurrentContinuityConnectivityPersists
    (d : ℕ) (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ R : ℕ, ∃ x : Site d,
    x ∉ box d R ∧
      epsilon ≤ StatMech.FK.infiniteTwoPointReal mu (Percolation.origin d) x


def CurrentContinuityPercolationPrinciple
    (d : ℕ) (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  0 < mu.real (percolationEvent d) →
    CurrentContinuityConnectivityPersists d mu


end StatMech.FrontierB
