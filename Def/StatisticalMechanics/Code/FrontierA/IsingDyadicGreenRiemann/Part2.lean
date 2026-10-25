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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

noncomputable def isingTorusMomentumGridEquiv (d k : Nat) :
    IsingDyadicTorus d k ≃
      ↑(isingNormalizedCoordinateCube d ∩
        ((isingDyadicSide k : Real)⁻¹ • isingUnitMomentumLattice d)) := by
  let f : IsingDyadicTorus d k →
      ↑(isingNormalizedCoordinateCube d ∩
        ((isingDyadicSide k : Real)⁻¹ • isingUnitMomentumLattice d)) :=
    fun p => ⟨isingTorusCenteredMomentumFun p,
      isingTorusCenteredMomentumFun_mem_cube p,
      isingTorusCenteredMomentumFun_mem_lattice p⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply isingTorusCenteredMomentumFun_injective
    exact congr_arg Subtype.val hpq
  · intro q
    obtain ⟨y, hyLattice, hyq⟩ := Set.mem_smul_set.mp q.property.2
    have hyInt : ∀ i : Fin d, ∃ z : Int, (z : Real) = y i := by
      intro i
      have hi := ((Pi.basisFun Real (Fin d)).mem_span_iff_repr_mem Int y).mp
        (show y ∈ Submodule.span Int
          (Set.range (Pi.basisFun Real (Fin d))) from hyLattice) i
      simpa only [Pi.basisFun_repr] using hi
    choose z hz using hyInt
    let p : IsingDyadicTorus d k :=
      fun i => (z i : ZMod (isingDyadicSide k))
    refine ⟨p, Subtype.ext ?_⟩
    funext i
    have hside : (0 : Real) < isingDyadicSide k := by
      exact_mod_cast isingDyadicSide_pos k
    have hcoord := congr_fun hyq i
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    have hqz : q.val i = (z i : Real) / isingDyadicSide k := by
      calc
        q.val i = (isingDyadicSide k : Real)⁻¹ * y i := hcoord.symm
        _ = (isingDyadicSide k : Real)⁻¹ * (z i : Real) := by rw [hz i]
        _ = (z i : Real) / isingDyadicSide k := by
          rw [div_eq_inv_mul, mul_comm]
    have hqCube := q.property.1 i
    have hlowReal : -(isingDyadicSide k : Real) <
        2 * (z i : Real) := by
      rw [hqz] at hqCube
      rw [lt_div_iff₀ hside] at hqCube
      nlinarith [hqCube.1]
    have huppReal : 2 * (z i : Real) ≤
        isingDyadicSide k := by
      rw [hqz] at hqCube
      rw [div_le_iff₀ hside] at hqCube
      nlinarith [hqCube.2]
    have hbounds : z i * 2 ∈
        Set.Ioc (-(isingDyadicSide k : Int)) (isingDyadicSide k : Int) := by
      constructor
      · have : -(isingDyadicSide k : Int) < 2 * z i := by
          exact_mod_cast hlowReal
        simpa [mul_comm] using this
      · have : 2 * z i ≤ (isingDyadicSide k : Int) := by
          exact_mod_cast huppReal
        simpa [mul_comm] using this
    have hpval :
        ((p i).valMinAbs : Int) = z i := by
      apply (ZMod.valMinAbs_spec (p i) (z i)).2
      refine ⟨?_, hbounds⟩
      change (z i : ZMod (isingDyadicSide k)) =
        (z i : ZMod (isingDyadicSide k))
      rfl
    change isingTorusCenteredMomentumFun p i = q.val i
    rw [isingTorusCenteredMomentumFun_apply, hpval]
    exact hqz.symm

end StatMech.FrontierA
