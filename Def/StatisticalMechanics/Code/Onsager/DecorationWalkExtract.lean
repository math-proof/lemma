/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycles


namespace StatMech.Onsager

def ons_decDartIsExternal {L : ℕ} (a : (ons_decGraph L).Dart) : Bool :=
  decide (a.snd = ons_dartRev L a.fst)

def ons_decWalkExternalDarts {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : List (ons_Dart L) :=
  (p.darts.filter ons_decDartIsExternal).map (fun a => a.fst)

end StatMech.Onsager
