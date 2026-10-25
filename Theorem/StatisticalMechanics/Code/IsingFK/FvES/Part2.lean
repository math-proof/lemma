/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.IsingFK.FvES
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


omit [DecidableRel G.Adj] in

theorem wiredColourEquiv_apply_val {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀)
    (σ : {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ}) (x : V) :
    (wiredColourEquiv G bdry b ω v₀ hv₀ σ).1 ((wiredSub G bdry ω).connectedComponentMk x)
      = σ.1 x := rfl


theorem sum_isingSpin : (∑ b : Fin 2, isingSpin b) = 0 := by
  simp [Fin.sum_univ_two, isingSpin]


end IsingFK
end StatMech
