/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMPClose.Part2
import Instance.StatisticalMechanics.Code.OSSS.SpliceST1
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem sp1_tailSplit_mp (n t : ℕ) :
    MeasurePreserving (sp1_tailDisint n t) (ubfTail n t)
      ((ubfTail n (t+1)).prod (Measure.pi (fun _ : sp1_Sing n t => unitMeasure))) := by
  unfold sp1_tailDisint
  
  have hsplit : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {i : Fin n // ¬ (i:ℕ) < t} => ℝ)
        (fun j => ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1))
      (ubfTail n t)
      ((Measure.pi (fun _ => unitMeasure)).prod (Measure.pi fun _ => unitMeasure)) := by
    show MeasurePreserving _ (Measure.pi (fun _ => unitMeasure)) _
    exact measurePreserving_piEquivPiSubtypeProd _ _
  
  have hren : MeasurePreserving (sp1_renTail n t)
      (Measure.pi (fun _ => unitMeasure)) (ubfTail n (t+1)) := by
    show MeasurePreserving _ _ (Measure.pi (fun _ => unitMeasure))
    exact measurePreserving_piCongrLeft (fun _ => unitMeasure) (sp1_idxEq n t)
  have hprod := hren.prod
    (MeasurePreserving.id (Measure.pi (fun _ : sp1_Sing n t => unitMeasure)))
  exact (show MeasurePreserving
      (MeasurableEquiv.prodCongr (sp1_renTail n t) (MeasurableEquiv.refl (sp1_Sing n t → ℝ)))
      _ _ from hprod).comp hsplit


end AdaptDisintegration
end OSSS
end StatMech
