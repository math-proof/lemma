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
import Def.StatisticalMechanics.Code.Universality.HVIntersection.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem hvMeet_of_separates (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (hsep : VSeparatesH ω α β m m' c d) : HVMeetProperty ω α β m m' c d := by
  classical
  intro hαm hmm' hm'β xL yR hcH xB yT hcV
  
  have hxBmem : (xB : Site 2) ∈ rect m m' c d := bottomSide_subset xB.2
  
  obtain ⟨wH⟩ := hcH
  
  have hx0 : ((⟨(xL : Site 2), leftSide_subset xL.2⟩ : rect α β c d) : Site 2) 0 = α :=
    xL.2.2
  have hy0 : ((⟨(yR : Site 2), rightSide_subset yR.2⟩ : rect α β c d) : Site 2) 0 = β :=
    yR.2.2
  
  obtain ⟨z, hzs, hzP⟩ := hsep hαm hmm' hm'β (xB : Site 2) hxBmem
    ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨(yR : Site 2), rightSide_subset yR.2⟩
    hx0 hy0 wH
  obtain ⟨hzO, hzVconn⟩ := hzP
  
  exact ⟨(z : Site 2), hzO, z.2, ⟨wH.takeUntil z hzs⟩, hzVconn⟩


theorem hv_intersection (ω : ConfigSpace (Sym2 (Site 2)))
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : VSeparatesH ω a m' m m' c d)
    (hsepR : VSeparatesH ω m b m m' c d) :
    HVIntersectionProperty ω a m m' b c d :=
  hvIntersection_of_meet ω ham hmm' hm'b
    (hvMeet_of_separates ω a m' m m' c d hsepL)
    (hvMeet_of_separates ω m b m m' c d hsepR)


theorem rsw_strip_glue_unconditional (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : ∀ ω, VSeparatesH ω a m' m m' c d)
    (hsepR : ∀ ω, VSeparatesH ω m b m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  rsw_strip_glue_of_intersection μ hpa
    (fun ω => hv_intersection ω ham hmm' hm'b (hsepL ω) (hsepR ω))

end Universality
end StatMech
