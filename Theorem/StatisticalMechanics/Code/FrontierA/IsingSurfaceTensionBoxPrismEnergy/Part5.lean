/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part4


namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

theorem fvEnergy_interface_eq_oddRectangularPrismDobrushinEnergy
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    fvEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
        (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) =
      oddRectangularPrismDobrushinEnergy 1 n sigma := by
  unfold fvEnergy oddRectangularPrismDobrushinEnergy
  simp only [zero_mul, sub_zero, neg_one_mul]
  change -(∑ edge ∈ bondFinsetTouch 3 n,
      bond (glue (interfaceField (⟨2, by omega⟩ : Fin 3))
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma)) edge) = _
  congr 1
  rw [sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex]
  calc
    (∑ q, bond (glue (interfaceField (⟨2, by omega⟩ : Fin 3))
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q)) =
        ∑ q, oddPrismDobrushinInteractionTerm n sigma q := by
      apply Finset.sum_congr rfl
      intro q _
      exact bond_glue_interface_oddPrismTouchIndex n hn sigma q
    _ = _ := sum_oddPrismDobrushinInteractionTerm n sigma

theorem oddRectangularPrismDobrushinEnergy_eq_mul_fvEnergy
    (J : Real) (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    oddRectangularPrismDobrushinEnergy J n sigma =
      J * fvEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
        (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
  rw [fvEnergy_interface_eq_oddRectangularPrismDobrushinEnergy n hn]
  unfold oddRectangularPrismDobrushinEnergy
  ring


theorem sum_rectangularPrismDobrushinCoupling_eq
    (J beta : Real) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ q : RectangularPrismInteraction (2 * n + 1) (2 * n + 1) n,
        rectangularPrismDobrushinCoupling J beta q *
          rectangularPrismInteractionMonomial q sigma) =
      -beta * oddRectangularPrismDobrushinEnergy J n sigma := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rectangularPrismDobrushinCoupling,
    rectangularPrismInteractionMonomial]
  simp_rw [Fintype.sum_prod_type]
  have hboundary :
      (∑ v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n,
          (if n < v.z.val then (-1 : Real) else 1) *
            (beta * J * rectangularPrismBoundaryDegree v) * spin sigma v) =
        beta * J *
          ∑ v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n,
            oddRectangularPrismDobrushinSign n v.z *
              (rectangularPrismBoundaryDegree v : Real) * spin sigma v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    unfold oddRectangularPrismDobrushinSign
    by_cases hz : n < v.z.val <;> simp [hz] <;> ring
  rw [hboundary,
    rectangularPrismDobrushinBoundaryInteraction_eq_faces]
  unfold oddRectangularPrismDobrushinEnergy
    rectangularPrismInternalInteraction rectangularPrismSpin
  simp_rw [← Finset.mul_sum]
  ring


theorem rectangularPrismDobrushinPartition_eq_fvZ
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    rectangularPrismDobrushinPartition J beta
        (2 * n + 1) (2 * n + 1) n =
      fvZ (interfaceField (⟨2, by omega⟩ : Fin 3)) n
        (bondFinsetTouch 3 n) (beta * J) 0 := by
  unfold rectangularPrismDobrushinPartition monomialInteractionPartition
    fvZ fvWeight
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sum_rectangularPrismDobrushinCoupling_eq,
    oddRectangularPrismDobrushinEnergy_eq_mul_fvEnergy J n hn]
  congr 1
  ring


theorem oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    StatMech.Ising.rectangularDobrushinFreeEnergy J beta
        (2 * n + 1) (2 * n + 1) n =
      finiteInterfaceFreeEnergy (⟨2, by omega⟩ : Fin 3) n (beta * J) := by
  rw [StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio]
  unfold finiteInterfaceFreeEnergy
  rw [rectangularPrismPlusPartition_eq_fvZ,
    rectangularPrismDobrushinPartition_eq_fvZ J beta n hn]


theorem standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
    (beta : Real) (n : Nat) (hn : 0 < n) :
    standardCubicInterfaceDensity beta n =
      rectangularPrismInterfaceDensity beta n := by
  unfold standardCubicInterfaceDensity rectangularPrismInterfaceDensity
  rw [oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy 1 beta n hn]
  simp


theorem hasStandardPrismSurfaceComparison (beta : Real) :
    HasStandardPrismSurfaceComparison beta := by
  unfold HasStandardPrismSurfaceComparison
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
    beta n (by omega), sub_self]


theorem hasDerivAt_oddPrismDobrushinFreeEnergy
    (J beta : Real) (n : Nat) (hn : 0 < n) :
    HasDerivAt
      (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b
        (2 * n + 1) (2 * n + 1) n)
      (J * (fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n)
          (beta * J) 0 -
        fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
          (bondFinsetTouch 3 n) (beta * J) 0)) beta := by
  have hfun :
      (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b
        (2 * n + 1) (2 * n + 1) n) =
      (fun b => finiteInterfaceFreeEnergy
        (⟨2, by omega⟩ : Fin 3) n (b * J)) := by
    funext b
    exact oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy J b n hn
  rw [hfun]
  convert
    (hasDerivAt_finiteInterfaceFreeEnergy
      (⟨2, by omega⟩ : Fin 3) n (beta * J)).comp beta
        ((hasDerivAt_id beta).mul_const J) using 1 <;>
    ring


theorem oddPrismDobrushinFreeEnergy_succ_eq_finiteInterfaceFreeEnergy
    (J beta : Real) (n : Nat) :
    StatMech.Ising.rectangularDobrushinFreeEnergy J beta
        (2 * (n + 1) + 1) (2 * (n + 1) + 1) (n + 1) =
      finiteInterfaceFreeEnergy (⟨2, by omega⟩ : Fin 3) (n + 1) (beta * J) :=
  oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy
    J beta (n + 1) (by omega)


theorem hasDerivAt_oddPrismDobrushinFreeEnergy_succ
    (J beta : Real) (n : Nat) :
    HasDerivAt
      (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b
        (2 * (n + 1) + 1) (2 * (n + 1) + 1) (n + 1))
      (J * (fvMeanNegEnergy (plusField 3) (n + 1)
          (bondFinsetTouch 3 (n + 1)) (beta * J) 0 -
        fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) (n + 1)
          (bondFinsetTouch 3 (n + 1)) (beta * J) 0)) beta :=
  hasDerivAt_oddPrismDobrushinFreeEnergy J beta (n + 1) (by omega)

end
end StatMech.FrontierA
