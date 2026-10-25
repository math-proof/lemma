/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Instance.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part2
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


def FiberMinorCandidate (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    (u v : W) : Prop :=
  Fintype.card (leftFiber ends m A B u v) ≤ Fintype.card (rightFiber ends m A B u v)


def GrahamFiberMinor (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) : Prop :=
  Fintype.card (leftFiber ends m {j, k} {k, l} k zero)
    ≤ Fintype.card (rightFiber ends m {j, k} {k, l} k zero)


noncomputable def rowSupportWeight (ends : ι → Sym2 W) (m K : Finset ι) : ℕ :=
  Fintype.card (boundarySector ends K ∅) *
    Fintype.card (boundarySector ends (m \ K) ∅)

def LeftRowSupport (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W)
    (K : Finset ι) : Prop :=
  Sharpness.RandomCurrent.sources ends K = {j, k} ∧
    Sharpness.RandomCurrent.sources ends (m \ K) = {k, l} ∧
    ¬ Sharpness.RandomCurrent.connK ends K k zero ∧
    ¬ Sharpness.RandomCurrent.connK ends (m \ K) k zero

def RightRowSupport (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W)
    (K : Finset ι) : Prop :=
  Sharpness.RandomCurrent.sources ends K = {j, k} ∆ {k, l} ∧
    (∃ P : Finset ι, P ⊆ K ∧ Sharpness.RandomCurrent.sources ends P = {j, k}) ∧
    Sharpness.RandomCurrent.sources ends (m \ K) = ∅ ∧
    ¬ Sharpness.RandomCurrent.connK ends K k zero ∧
    ¬ Sharpness.RandomCurrent.connK ends (m \ K) k zero

noncomputable def leftRowSupports (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Finset (Finset ι) := by
  classical
  exact m.powerset.filter (LeftRowSupport ends m j k l zero)

noncomputable def rightRowSupports (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Finset (Finset ι) := by
  classical
  exact m.powerset.filter (RightRowSupport ends m j k l zero)


noncomputable def GrahamWeightedRowMinor (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Prop := by
  classical
  exact
    (∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K)
      ≤ ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K

def leftRowSupportIndex (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) :=
  {K : Finset ι // K ⊆ m ∧ LeftRowSupport ends m j k l zero K}

def leftRowData (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) :=
  Σ K : leftRowSupportIndex ends m j k l zero,
    boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) {k, l}

end FourColor
end GrahamGHS
end StatMech
