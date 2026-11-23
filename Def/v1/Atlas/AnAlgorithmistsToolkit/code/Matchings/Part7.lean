/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Analysis.Convex.Birkhoff
public import Instance.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part4

@[expose] public section

open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

def HasConductanceLB {V : Type*} [Fintype V] [DecidableEq V]
    (cutEdges : Finset V → ℝ) (vol : Finset V → ℝ) (c : ℝ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    cutEdges S / min (vol S) (vol (Finset.univ \ S)) ≥ c

def HasConductanceUB {V : Type*} [Fintype V] [DecidableEq V]
    (cutEdges : Finset V → ℝ) (vol : Finset V → ℝ) (c : ℝ) : Prop :=
  ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧
    cutEdges S / min (vol S) (vol (Finset.univ \ S)) ≤ c


noncomputable def chainDegree {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (v : ChainVertex G) : ℕ :=
  (neighbors v).card

noncomputable def chainVol {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (S : Finset (ChainVertex G)) : ℝ :=
  ∑ v ∈ S, (chainDegree neighbors v : ℝ)

noncomputable def chainCutEdges {n : ℕ} {G : BipartiteGraph n}
    (neighbors : ChainVertex G → Finset (ChainVertex G))
    (S : Finset (ChainVertex G)) : ℝ :=
  ∑ v ∈ S, ((neighbors v).filter (fun w => w ∉ S)).card

def permanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i)

end PartialMatching
end Matchings
