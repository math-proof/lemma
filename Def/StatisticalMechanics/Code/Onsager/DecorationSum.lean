module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
public import Abbrev.StatisticalMechanics.Code.Onsager.DecorationSum


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_originalEdgesOfDecorated
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  ((ons_decorationEquiv L).symm D).1

end StatMech.Onsager
