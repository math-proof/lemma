/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


theorem torusCellPrimalOfDualEdge_of_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L e =
      ((torusCellCrossing L).symm ⟨e, he⟩ : TorusAmbientEdge L) := by
  simp [torusCellPrimalOfDualEdge, he]


theorem torusCellPrimalOfDualEdge_mem (L : ℕ) [Fact (2 < L)]
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L e ∈ (onsTorusGraph L).edgeFinset := by
  rw [torusCellPrimalOfDualEdge_of_mem L he]
  exact ((torusCellCrossing L).symm ⟨e, he⟩).2


theorem torusCellPrimalOfDualEdge_injOn (L : ℕ) [Fact (2 < L)] :
    Set.InjOn (torusCellPrimalOfDualEdge L)
      (↑(onsTorusGraph L).edgeFinset : Set (Sym2 (ZMod L × ZMod L))) := by
  intro e he e' he' h
  have he0 : e ∈ (onsTorusGraph L).edgeFinset := he
  have he1 : e' ∈ (onsTorusGraph L).edgeFinset := he'
  rw [torusCellPrimalOfDualEdge_of_mem L he0,
    torusCellPrimalOfDualEdge_of_mem L he1] at h
  exact congrArg Subtype.val ((torusCellCrossing L).symm.injective
    (Subtype.ext h))


end StatMech.BeffaraDC
