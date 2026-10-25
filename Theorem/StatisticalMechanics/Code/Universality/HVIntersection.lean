/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HVIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Def.StatisticalMechanics.Code.Universality.HVIntersection
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem hvIntersection_of_meet (ω : ConfigSpace (Sym2 (Site 2)))
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hmeetL : HVMeetProperty ω a m' m m' c d)
    (hmeetR : HVMeetProperty ω m b m m' c d) :
    HVIntersectionProperty ω a m m' b c d := by
  intro hH hV hHr
  
  obtain ⟨xL, pR, hcL⟩ := hH          
  obtain ⟨xB, yT, hcV⟩ := hV          
  obtain ⟨qL, yR, hcR⟩ := hHr         
  
  obtain ⟨p, hpO, hpL, hcLp, hcVp⟩ :=
    hmeetL ham hmm' le_rfl xL pR hcL xB yT hcV
  
  obtain ⟨q, hqO, hqR, hcRq, hcVq⟩ :=
    hmeetR le_rfl hmm' hm'b qL yR hcR xB yT hcV
  
  have hcPQ : ConnectedWithin 2 ω (rect m m' c d) ⟨p, hpO⟩ ⟨q, hqO⟩ :=
    hcVp.symm.trans hcVq
  
  have hcQyR : ConnectedWithin 2 ω (rect m b c d) ⟨q, hqR⟩
      ⟨(yR : Site 2), rightSide_subset yR.2⟩ := hcRq.symm.trans hcR
  
  exact hv_glue ham hm'b xL.2 hpO hpL hcLp hqO hcPQ yR.2 hqR hcQyR


end Universality
end StatMech
