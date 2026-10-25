/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZero
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open scoped BigOperators
open Filter Topology Finset SimpleGraph


namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable def sctBoxCovariance (d : ℕ) (beta h : ℝ) (n : ℕ)
    (x : sctBox d n) : ℝ :=
  isingExpectation (sctBoxGraph d n) beta h
      (fun s => spin s (sctBoxOrigin d n) * spin s x) -
    sctOriginMag d beta h n * sctBoxMag d beta h n x


noncomputable def sctExteriorNeighbours (d n : ℕ) (x : Site d) : Finset (Site d) :=
  ((hypercubicLattice d).neighborFinset x).filter (fun y => y ∉ box d n)


noncomputable def sctBoundaryCovarianceError (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  ∑ x : sctBox d n,
    ((sctExteriorNeighbours d n x.1).card : ℝ) * sctBoxCovariance d beta h n x


noncomputable def sctOuterCovarianceSum (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  ∑ x : sctBox d n,
    if x.1 ∈ box d (n - 1) then 0 else sctBoxCovariance d beta h n x


def sctInnerField (d : ℕ) (beta h : ℝ) (n : ℕ) (x : sctBox d n) : ℝ :=
  if x.1 ∈ box d (n - 1) then beta * h else 0


def sctOuterDirection (d n : ℕ) (x : sctBox d n) : ℝ :=
  if x.1 ∈ box d (n - 1) then 0 else 1


noncomputable def sctInnerFieldMag (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  expJ (sctBoxGraph d n).edgeFinset (fun _ => beta)
    (sctInnerField d beta h n) (fun s => spin s (sctBoxOrigin d n))


end Sharpness
end StatMech
