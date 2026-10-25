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


namespace StatMech.Onsager

open BigOperators StatMech.Ising

abbrev ons_TorusEvenSubgraph (L : ℕ) [Fact (2 < L)] :=
  {F : Finset (Sym2 (ZMod L × ZMod L)) //
    F ∈ evenSubgraphs (onsTorusGraph L)}

abbrev ons_DecoratedEvenSubgraph (L : ℕ) [Fact (2 < L)] :=
  {D : Finset (Sym2 (ons_Dart L)) //
    D ∈ evenSubgraphs (ons_decGraph L)}


end StatMech.Onsager
