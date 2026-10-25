/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeInjective
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectListFlatMapReplicate
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry.Part3


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitRibbonSubdivisionSite_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Function.Injective
      (fkRectBlackOrbitRibbonSubdivisionSite R omega d) := by
  letI : NeZero (8 * R.medialTorus.width) :=
    ⟨(mul_pos (by decide) R.medialTorus.width_pos).ne'⟩
  letI : NeZero (8 * R.medialTorus.height) :=
    ⟨(mul_pos (by decide) R.medialTorus.height_pos).ne'⟩
  intro z w h
  apply fkRectBlackOrbitRibbonSubdivisionCode_injective R omega d
  apply fkRectRibbonSubdivisionCodeEmbed_injective
    (8 * R.medialTorus.width) (8 * R.medialTorus.height)
  exact (Equiv.cast (congrArg (fun n => ZMod n × ZMod n)
    (fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct R))).injective h

end
end StatMech.FrontierD
