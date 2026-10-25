/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSimonMass
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointReduction
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityMagnetizationFK
open Finset MeasureTheory Set


namespace StatMech.FrontierA

open Ising Lattice Percolation Sharpness

open StatMech.FrontierB


theorem isingExpectation_instance_irrel
    {V : Type*} (i j : Fintype V) (deqI deqJ : DecidableEq V)
    (G : SimpleGraph V) (adjI adjJ : DecidableRel G.Adj)
    (beta h : Real) (f : ConfigSpace V → Real) :
    @isingExpectation V i deqI G adjI beta h f =
      @isingExpectation V j deqJ G adjJ beta h f := by
  have hi : i = j := Subsingleton.elim _ _
  subst j
  have hdeq : deqI = deqJ := Subsingleton.elim _ _
  subst deqJ
  have hadj : adjI = adjJ := Subsingleton.elim _ _
  subst adjJ
  rfl


theorem corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint
    (d n : Nat) (beta : Real) (x : Site d)
    (hx : x ∈ box d n) (hxo : x ≠ Percolation.origin d) :
    corrOriginInner d beta (boxSV_boxF d n) x =
      currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) x := by
  classical
  have h0 : Percolation.origin d ∈ boxSV_boxF d n := by
    change Percolation.origin d ∈ (boxSV_boxF d n : Set (Site d))
    rw [boxSV_coe_boxF]
    exact origin_mem_box' n
  have hxF : x ∈ boxSV_boxF d n := by
    change x ∈ (boxSV_boxF d n : Set (Site d))
    rw [boxSV_coe_boxF]
    exact hx
  let oF : {z : Site d // z ∈ boxSV_boxF d n} :=
    ⟨Percolation.origin d, h0⟩
  let xF : {z : Site d // z ∈ boxSV_boxF d n} := ⟨x, hxF⟩
  have hox : oF ≠ xF := by
    intro h
    apply hxo
    exact congrArg Subtype.val h |>.symm
  unfold corrOriginInner
  rw [dif_pos h0, dif_pos hxF]
  rw [freeCorr, if_neg hox]
  unfold currentContinuityFreeBoxTwoPoint
  rw [integral_freeMeasure_spinProd_eq_freeDomain d n beta
    ({Percolation.origin d, x} : Finset _)]
  · rw [show Ising.boxFinset d n = boxSV_boxF d n by
      rw [boxSV_boxF_eq_toFinset]
      rfl]
    have hsupp : ({oF, xF} : Finset _) =
        freeDomainSpinSupport (boxSV_boxF d n)
          {Percolation.origin d, x} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton,
        freeDomainSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (hz | hz)
        · left
          exact Subtype.ext hz
        · right
          exact Subtype.ext hz
    have hsupp' :
        ({⟨Percolation.origin d, h0⟩, ⟨x, hxF⟩} : Finset _) =
          freeDomainSpinSupport (boxSV_boxF d n)
            {Percolation.origin d, x} := by
      simpa [oF, xF] using hsupp
    rw [hsupp']
    exact isingExpectation_instance_irrel
      (Finset.Subtype.fintype (boxSV_boxF d n))
      (freeDomainVerticesFintype (boxSV_boxF d n))
      (fun a b => a.instDecidableEq b) (fun a b => a.instDecidableEq b)
      (graphS d (boxSV_boxF d n))
      (instDecidableAdjGraphS d (boxSV_boxF d n))
      (freeDomainGraphDecidableAdj (boxSV_boxF d n)) beta 0 _
  · intro z hz
    rw [show Ising.boxFinset d n = boxSV_boxF d n by
      rw [boxSV_boxF_eq_toFinset]
      rfl]
    have hz' : z = Percolation.origin d ∨ z = x := by simpa using hz
    exact hz'.elim (fun h => h ▸ h0) (fun h => h ▸ hxF)


theorem corrOriginInner_box_le_currentContinuityFreeTwoPoint
    (d n : Nat) (beta : Real) (hbeta : 0 ≤ beta) (x : Site d)
    (hx : x ∈ box d n) (hxo : x ≠ Percolation.origin d) :
    corrOriginInner d beta (boxSV_boxF d n) x ≤
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  rw [corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint
    d n beta x hx hxo]
  apply currentContinuityFreeBoxTwoPoint_le_freeTwoPoint beta hbeta
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rw [show Ising.boxFinset d n = boxSV_boxF d n by
    rw [boxSV_boxF_eq_toFinset]
    rfl]
  change z ∈ (boxSV_boxF d n : Set (Site d))
  rw [boxSV_coe_boxF]
  exact hz.elim (fun h => h ▸ origin_mem_box' n) (fun h => h ▸ hx)


end StatMech.FrontierA
