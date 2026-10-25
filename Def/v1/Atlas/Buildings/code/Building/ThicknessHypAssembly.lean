/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessHypAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.ThicknessFoldings
import Lemma.List.Any.of.Any_Not.Ne.IsChain
import Theorem.v1.Atlas.Buildings.code.Building.ThicknessHypAssembly
open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AptIsCoxeterProof

/-- Promote `PreApartmentData` to a full `ApartmentSystem`, given thickness
and the Tits theorem hypothesis. -/
def PreApartmentData.toApartmentSystem' {K : ChamberComplex V}
    (pre : PreApartmentData K) (hThick : K.IsThick)
    (tits_thm : TitsTheoremHyp V) :
    ApartmentSystem K :=
  pre.toApartmentSystem hThick tits_thm thickness_hyp

end AptIsCoxeterProof
