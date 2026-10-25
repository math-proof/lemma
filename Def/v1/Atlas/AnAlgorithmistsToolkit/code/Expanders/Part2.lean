/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Expanders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders


namespace SpectralExpanders

attribute [instance] GraphFamily.instFintype GraphFamily.instDecidableEq
  GraphFamily.instDecidableAdj

open Finset BigOperators

noncomputable def GraphFamily.setConductanceAt (F : GraphFamily) (n : ℕ)
    (S : Finset (F.V n)) : ℝ :=
  let volS := ∑ v ∈ S, ((F.G n).degree v : ℝ)
  let volSc := ∑ v ∈ Sᶜ, ((F.G n).degree v : ℝ)
  let edgesCut := ∑ v ∈ S, (((F.G n).neighborFinset v) \ S).card
  (edgesCut : ℝ) / min volS volSc

noncomputable def GraphFamily.familyConductance (F : GraphFamily) (n : ℕ) : ℝ :=
  let candidates := (@Finset.univ (Finset (F.V n)) _).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ)
  if h : candidates.Nonempty then
    candidates.inf' h (F.setConductanceAt n)
  else
    0

def IsExpanderFamilyConductance (F : GraphFamily) : Prop :=
  ∃ c' : ℝ, c' > 0 ∧ ∀ n : ℕ, F.familyConductance n ≥ c'

end SpectralExpanders

namespace SimpleGraph

section BipartiteExpander

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

variable (G : SimpleGraph (L ⊕ R)) [DecidableRel G.Adj]

def bipartiteNeighborFinset (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => ∃ l ∈ S, G.Adj (Sum.inl l) (Sum.inr r)

def IsBipartiteExpander (α β : ℝ) : Prop :=
  ∀ S : Finset L, (S.card : ℝ) ≤ α * (Fintype.card L : ℝ) →
    ((G.bipartiteNeighborFinset S).card : ℝ) ≥ β * (S.card : ℝ)

end BipartiteExpander
end SimpleGraph
