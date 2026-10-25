/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part3


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_walkExternalEdges {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : Finset (Sym2 (ons_Dart L)) :=
  ons_decoratedExternalEdges p.edges.toFinset

noncomputable def ons_walkOriginalEdges {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  (ons_walkExternalEdges p).image ons_decEdgeProjection

end StatMech.Onsager
