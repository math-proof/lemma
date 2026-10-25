/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal
open Filter Finset Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem pairCorrelation_self
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (x : V) :
    expectationJ G beta J (grahamPairSupport x x) = 1 := by
  simpa [twoPointJ, grahamPairSupport] using
    twoPointJ_self G beta J x

theorem pairCorrelation_comm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (x y : V) :
    expectationJ G beta J (grahamPairSupport x y) =
      expectationJ G beta J (grahamPairSupport y x) := by
  unfold grahamPairSupport
  rw [symmDiff_comm]

theorem finiteParityFourthUrsell_eq_of_firstPair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i k l : V) :
    finiteParityFourthUrsell G beta J i i k l =
      -2 * expectationJ G beta J (grahamPairSupport i k) *
        expectationJ G beta J (grahamPairSupport i l) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i i ∆ grahamPairSupport k l =
      grahamPairSupport k l by simp [grahamPairSupport]]
  rw [pairCorrelation_self]
  ring

theorem finiteParityFourthUrsell_eq_of_secondPair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j l : V) :
    finiteParityFourthUrsell G beta J i j j l =
      -2 * expectationJ G beta J (grahamPairSupport j i) *
        expectationJ G beta J (grahamPairSupport j l) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [grahamPairSupport_chain]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J i j]
  ring

theorem finiteParityFourthUrsell_eq_of_firstThird
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j l : V) :
    finiteParityFourthUrsell G beta J i j i l =
      -2 * expectationJ G beta J (grahamPairSupport i j) *
        expectationJ G beta J (grahamPairSupport i l) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i j ∆ grahamPairSupport i l =
      grahamPairSupport j l by
    rw [show grahamPairSupport i j = grahamPairSupport j i by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    exact grahamPairSupport_chain j i l]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J j i]
  ring

theorem finiteParityFourthUrsell_eq_of_firstFourth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k : V) :
    finiteParityFourthUrsell G beta J i j k i =
      -2 * expectationJ G beta J (grahamPairSupport i j) *
        expectationJ G beta J (grahamPairSupport i k) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i j ∆ grahamPairSupport k i =
      grahamPairSupport j k by
    rw [show grahamPairSupport i j = grahamPairSupport j i by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    rw [show grahamPairSupport k i = grahamPairSupport i k by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    exact grahamPairSupport_chain j i k]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J j i,
    pairCorrelation_comm G beta J k i]
  ring

theorem finiteParityFourthUrsell_eq_of_secondFourth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k : V) :
    finiteParityFourthUrsell G beta J i j k j =
      -2 * expectationJ G beta J (grahamPairSupport j i) *
        expectationJ G beta J (grahamPairSupport j k) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i j ∆ grahamPairSupport k j =
      grahamPairSupport i k by
    rw [show grahamPairSupport k j = grahamPairSupport j k by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    exact grahamPairSupport_chain i j k]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J i j,
    pairCorrelation_comm G beta J k j]
  ring

theorem finiteParityFourthUrsell_eq_of_thirdPair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k : V) :
    finiteParityFourthUrsell G beta J i j k k =
      -2 * expectationJ G beta J (grahamPairSupport k i) *
        expectationJ G beta J (grahamPairSupport k j) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport k k = ∅ by simp [grahamPairSupport]]
  rw [show grahamPairSupport i j ∆ (∅ : Finset V) =
      grahamPairSupport i j by
    ext x
    simp [Finset.mem_symmDiff]]
  rw [show expectationJ G beta J (∅ : Finset V) = 1 by
    simpa [grahamPairSupport] using pairCorrelation_self G beta J k]
  rw [pairCorrelation_comm G beta J i k,
    pairCorrelation_comm G beta J j k]
  ring

theorem pairCorrelation_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (x y : V) :
    0 ≤ expectationJ G beta J (grahamPairSupport x y) := by
  rw [current_representation]
  exact div_nonneg
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)


end
end StatMech.FrontierA
