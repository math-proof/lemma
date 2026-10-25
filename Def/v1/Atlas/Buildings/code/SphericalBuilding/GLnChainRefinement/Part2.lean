/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnChainRefinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement.Part2


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Given a base flag and a single-subspace insertion hypothesis, refine any finite list of
proper subspaces into a single maximal flag containing all of them, by inductively
inserting them one at a time. -/
noncomputable def latticeChainRefinementOfInsertion
    (base : BaseFlagHyp k n)
    (ins : FlagInsertionHyp k n) : LatticeChainRefinementHyp k n where
  refine_via_chain := fun subs hproper => by
    induction subs with
    | nil =>
      exact ⟨base.base_chain,
        fun _ h => absurd h (List.not_mem_nil),
        base.base_chain_is_chain,
        base.base_chain_length,
        base.base_chain_proper⟩
    | cons V rest ih =>
      have hV_proper := hproper V List.mem_cons_self
      have hrest_proper : ∀ W ∈ rest, W ≠ ⊥ ∧ W ≠ ⊤ :=
        fun W hW => hproper W (List.mem_cons_of_mem V hW)
      obtain ⟨chain₀, hcontains₀, hchain₀, hlen₀, hproper₀⟩ := ih hrest_proper
      obtain ⟨chain₁, hV_mem, hold_mem, hchain₁, hlen₁, hproper₁⟩ :=
        ins.insert chain₀ V hchain₀ hlen₀ hproper₀ hV_proper.1 hV_proper.2
      exact ⟨chain₁,
        fun W hW => by
          rcases List.mem_cons.mp hW with heq | hrest
          · exact heq ▸ hV_mem
          · exact hold_mem W (hcontains₀ W hrest),
        hchain₁,
        hlen₁,
        hproper₁⟩

end GLnBuilding
