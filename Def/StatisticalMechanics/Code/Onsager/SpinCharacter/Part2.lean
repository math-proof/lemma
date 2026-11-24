module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
public import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
public import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_spinCharacterSum (L : ℕ) [Fact (2 < L)]
    (x : ℝ) (a b : Fin 2) : ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card

end StatMech.Onsager
