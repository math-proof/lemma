/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal
open Filter Finset Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def finiteCollisionFourthMajorant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k l : V) : Real :=
  let C := fun x y => expectationJ G beta J (grahamPairSupport x y)
  2 * ((if i = j then C i k * C i l else 0) +
    (if i = k then C i j * C i l else 0) +
    (if i = l then C i j * C i k else 0) +
    (if j = k then C j i * C j l else 0) +
    (if j = l then C j i * C j k else 0) +
    (if k = l then C k i * C k j else 0))


def finiteCollisionFourthWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k l : V) : Real :=
  if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then 0
  else -finiteParityFourthUrsell G beta J i j k l

end
end StatMech.FrontierA
