/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentChainClosure
import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentAxisPersistence
open Filter MeasureTheory Set Topology
open scoped symmDiff


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation Sharpness

open StatMech.OSSS.FKSharpnessWeightedPhaseTransport

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


noncomputable def currentContinuityAxisSite
    {d : Nat} (hd : 1 ≤ d) (k : Nat) : Site d :=
  (FK.freeAxisTranslationPower hd k)⁻¹ • origin d


def CurrentContinuityFreeAxisLROZero
    (d : Nat) (hd : 1 ≤ d) (beta : Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ K : Nat, ∀ k : Nat, K ≤ k →
    |currentContinuityFreeTwoPoint d beta (origin d)
      (currentContinuityAxisSite hd k)| < epsilon


def CurrentContinuityAxisConnectivityPersists
    (d : Nat) (hd : 1 ≤ d)
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∃ epsilon : Real, 0 < epsilon ∧ ∀ K : Nat, ∃ k : Nat, K ≤ k ∧
    epsilon ≤ infiniteTwoPointReal mu (origin d)
      (currentContinuityAxisSite hd k)

def CurrentContinuityAxisPercolationPrinciple
    (d : Nat) (hd : 1 ≤ d)
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  0 < mu.real (percolationEvent d) →
    CurrentContinuityAxisConnectivityPersists d hd mu


end StatMech.FrontierB
