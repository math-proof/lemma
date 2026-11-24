module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
public import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable instance ons_xSeamEdge_decidable {L : ℕ}
    (e : Sym2 (ZMod L × ZMod L)) : Decidable (ons_xSeamEdge L e) :=
  Classical.propDecidable _

noncomputable instance ons_ySeamEdge_decidable {L : ℕ}
    (e : Sym2 (ZMod L × ZMod L)) : Decidable (ons_ySeamEdge L e) :=
  Classical.propDecidable _


end StatMech.Onsager
