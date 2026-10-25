/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonClassification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


theorem fkMedialBlackDartSwap_vertex
    (v : T.Vertex) (d : FKMedialBlackDart T) :
    ((fkMedialBlackDartSwap v d).1).1 = d.1.1 := by
  by_cases h0 : d = fkMedialBlackDart0 v
  · subst d
    simp [fkMedialBlackDartSwap, fkMedialBlackDart0,
      fkMedialBlackDart1]
  by_cases h1 : d = fkMedialBlackDart1 v
  · subst d
    simp [fkMedialBlackDartSwap, fkMedialBlackDart0,
      fkMedialBlackDart1]
  rw [fkMedialBlackDartSwap,
    Equiv.swap_apply_of_ne_of_ne h0 h1]


theorem fkMedialBlackDartSwap_apply_of_vertex_ne
    (v : T.Vertex) (d : FKMedialBlackDart T) (hd : d.1.1 ≠ v) :
    fkMedialBlackDartSwap v d = d := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hd (congrArg (fun x : FKMedialBlackDart T => x.1.1) h)
  · intro h
    exact hd (congrArg (fun x : FKMedialBlackDart T => x.1.1) h)


theorem fkMedialBlackDartSwap_commute
    {v w : T.Vertex} (hvw : v ≠ w) :
    Commute (fkMedialBlackDartSwap v) (fkMedialBlackDartSwap w) := by
  show fkMedialBlackDartSwap v * fkMedialBlackDartSwap w =
    fkMedialBlackDartSwap w * fkMedialBlackDartSwap v
  apply Equiv.ext
  intro d
  simp only [Equiv.Perm.mul_apply]
  by_cases hdv : d.1.1 = v
  · have hdw : d.1.1 ≠ w := fun h => hvw (hdv.symm.trans h)
    rw [fkMedialBlackDartSwap_apply_of_vertex_ne w d hdw]
    have hsw : ((fkMedialBlackDartSwap v d).1).1 ≠ w := by
      rw [fkMedialBlackDartSwap_vertex v d]
      exact hdw
    rw [fkMedialBlackDartSwap_apply_of_vertex_ne w _ hsw]
  · by_cases hdw : d.1.1 = w
    · rw [fkMedialBlackDartSwap_apply_of_vertex_ne v d hdv]
      have hsv : ((fkMedialBlackDartSwap w d).1).1 ≠ v := by
        rw [fkMedialBlackDartSwap_vertex w d]
        exact hdv
      rw [fkMedialBlackDartSwap_apply_of_vertex_ne v _ hsv]
    · simp only [fkMedialBlackDartSwap_apply_of_vertex_ne v d hdv,
        fkMedialBlackDartSwap_apply_of_vertex_ne w d hdw]


end
end StatMech.FrontierD
