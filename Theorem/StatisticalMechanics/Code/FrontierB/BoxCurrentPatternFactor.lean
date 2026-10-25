/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
import Def.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

theorem restrictCurrent_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (m : EdgeCurrent (StatMech.FK.boxGraph d (n + 1))) :
    restrictCurrent F (extendBoxCurrent d (n + 1) m) =
      pushforwardBoxLocalCurrent d n F hF
        (restrictCurrent (boxPullbackEdgeSubtypes d n F) m) := by
  funext e
  let f := (boxPullbackEdgeEquiv d n F hF).symm e
  have hincl : StatMech.FK.edgeIncl d (n + 1) f.1.1 = e.1 :=
    congrArg Subtype.val
      ((boxPullbackEdgeEquiv d n F hF).apply_symm_apply e)
  change extendBoxCurrent d (n + 1) m e.1 = m f.1
  rw [← hincl]
  change extendBoxCurrent d (n + 1) m
    (boxCurrentEdgeIncl d (n + 1) f.1) = m f.1
  exact extendBoxCurrent_included d (n + 1) m f.1

theorem finiteParityKernel_pullbackCurrentPattern
    (d n : ℕ) (beta : ℝ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (a : ↑F → ℕ) :
    finiteParityKernel (boxPullbackEdgeSubtypes d n F) beta
        (currentLocalParity (pullbackCurrentPattern d n F hF a))
        (pullbackCurrentPattern d n F hF a) =
      finiteParityKernel F beta (currentLocalParity a) a := by
  unfold finiteParityKernel
  apply Fintype.prod_equiv (boxPullbackEdgeEquiv d n F hF)
  intro i
  rfl

theorem preimage_currentCylinder_singleton_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (a : ↑F → ℕ) :
    extendBoxCurrent d (n + 1) ⁻¹' currentCylinder F {a} =
      {m | restrictCurrent (boxPullbackEdgeSubtypes d n F) m =
        pullbackCurrentPattern d n F hF a} := by
  ext m
  simp only [Set.mem_preimage, currentCylinder, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro hm
    funext f
    have hc := congrFun hm (boxPullbackEdgeEquiv d n F hF f)
    change extendBoxCurrent d (n + 1) m
        (boxPullbackEdgeEquiv d n F hF f).1 =
      a (boxPullbackEdgeEquiv d n F hF f) at hc
    change m f.1 = a (boxPullbackEdgeEquiv d n F hF f)
    rw [← hc]
    change m f.1 = extendBoxCurrent d (n + 1) m
      (StatMech.FK.edgeIncl d (n + 1) f.1.1)
    symm
    exact extendBoxCurrent_included d (n + 1) m f.1
  · intro hm
    funext e
    let f := (boxPullbackEdgeEquiv d n F hF).symm e
    have hc := congrFun hm f
    have hincl : StatMech.FK.edgeIncl d (n + 1) f.1.1 = e.1 :=
      congrArg Subtype.val
        ((boxPullbackEdgeEquiv d n F hF).apply_symm_apply e)
    change extendBoxCurrent d (n + 1) m e.1 = a e
    rw [← hincl]
    change extendBoxCurrent d (n + 1) m
      (boxCurrentEdgeIncl d (n + 1) f.1) = a e
    rw [extendBoxCurrent_included d (n + 1) m f.1]
    simpa [pullbackCurrentPattern, f] using hc

theorem currentLocalParity_restrictCurrent_eq_restrictParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset G.edgeFinset) (m : EdgeCurrent G) :
    currentLocalParity (restrictCurrent S m) =
      restrictParity G S (currentParitySupport G m) := by
  funext e
  simp only [currentLocalParity, restrictCurrent, restrictParity]
  by_cases hodd : Odd (m e.1)
  · have hmem : e.1.1 ∈ currentParitySupport G m :=
      (mem_currentParitySupport G m e.1).2 hodd
    simp [hodd, hmem]
  · have hmem : e.1.1 ∉ currentParitySupport G m := fun h =>
      hodd ((mem_currentParitySupport G m e.1).1 h)
    simp [hodd, hmem]

theorem boundaryCurrentLocalParityPMF
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (S : Finset G.edgeFinset) :
    PMF.map currentLocalParity
        (PMF.map (restrictCurrent S)
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) interior)) =
      PMF.map (restrictParity G S)
        (boundaryParityPMF G beta hbeta.le interior) := by
  rw [boundaryParityPMF, PMF.map_comp, PMF.map_comp]
  congr 1
  funext m
  exact currentLocalParity_restrictCurrent_eq_restrictParity G S m

theorem sourcelessCurrentLocalParityPMF
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 < beta) (S : Finset G.edgeFinset) :
    PMF.map currentLocalParity
        (PMF.map (restrictCurrent S)
          (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one))) =
      PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le) := by
  rw [← sourcelessCurrentPMF_map_currentParitySupport,
    PMF.map_comp, PMF.map_comp]
  congr 1
  funext m
  exact currentLocalParity_restrictCurrent_eq_restrictParity G S m

end StatMech.FrontierB
