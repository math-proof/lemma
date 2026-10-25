/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Def.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

theorem isingTorusCenteredMomentumFun_mem_cube
    {k : Nat} (p : IsingDyadicTorus d k) :
    isingTorusCenteredMomentumFun p ∈
      isingNormalizedCoordinateCube d := by
  intro i
  have h := isingTorusCenteredMomentum_mem p i
  simpa only [isingTorusCenteredMomentum_apply,
    isingTorusCenteredMomentumFun_apply] using h

theorem isingTorusCenteredMomentumFun_mem_lattice
    {k : Nat} (p : IsingDyadicTorus d k) :
    isingTorusCenteredMomentumFun p ∈
      ((isingDyadicSide k : Real)⁻¹ • isingUnitMomentumLattice d) := by
  let y : IsingMomentumCoordinates d :=
    fun i => ((p i).valMinAbs : Real)
  have hy : y ∈ isingUnitMomentumLattice d := by
    rw [isingUnitMomentumLattice,
      (Pi.basisFun Real (Fin d)).mem_span_iff_repr_mem Int]
    intro i
    rw [Pi.basisFun_repr]
    exact ⟨(p i).valMinAbs, rfl⟩
  change isingTorusCenteredMomentumFun p ∈
    (isingDyadicSide k : Real)⁻¹ •
      (↑(isingUnitMomentumLattice d) : Set (IsingMomentumCoordinates d))
  rw [Set.mem_smul_set]
  refine ⟨y, hy, ?_⟩
  funext i
  simp only [Pi.smul_apply, smul_eq_mul,
    isingTorusCenteredMomentumFun_apply]
  dsimp [y]
  rw [div_eq_inv_mul]


end StatMech.FrontierA
