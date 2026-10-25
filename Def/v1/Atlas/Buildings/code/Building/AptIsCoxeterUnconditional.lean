/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptIsCoxeterUnconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.ThicknessHypAssembly
import Lemma.Set.Any_EqToSimplicialComplexAndAny_And_All_Any_And_EqAndAll_ChamberAdjacentAndIsThin.of.In_Apartments.IsThick
import Lemma.Fin.TitsTheoremHypV
import Theorem.v1.Atlas.Buildings.code.Building.TitsTheoremAssembly
open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AptIsCoxeterProof

/-- Unconditional construction of an `ApartmentSystem` from `PreApartmentData` via the assembled
Tits theorem and thickness hypotheses. -/
def PreApartmentData.toApartmentSystemUnconditional {K : ChamberComplex V}
    (pre : PreApartmentData K) (hThick : K.IsThick) :
    ApartmentSystem K :=
  pre.toApartmentSystem hThick tits_theorem_hyp thickness_hyp

end AptIsCoxeterProof
