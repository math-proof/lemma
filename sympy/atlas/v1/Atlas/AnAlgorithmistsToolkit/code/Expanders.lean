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

namespace Expanders

abbrev IsDRegular {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) : Prop :=
  G.IsRegularOfDegree d

variable {V : Type*} [DecidableEq V]

noncomputable def indicatorVec (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

end Expanders

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def setNeighborFinset (S : Finset V) : Finset V :=
  (S.biUnion (fun v => G.neighborFinset v)) \ S

def IsVertexExpander (α β : ℝ) : Prop :=
  α * β < 1 ∧
  ∀ S : Finset V, (S.card : ℝ) ≤ α * (Fintype.card V : ℝ) →
    ((G.setNeighborFinset S).card : ℝ) ≥ β * (S.card : ℝ)

open Matrix Finset BigOperators

noncomputable def edgeCountBetween (S T : Finset V) : ℕ :=
  ((S ×ˢ T).filter fun p => G.Adj p.1 p.2).card

noncomputable def adjEigenvalues : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

noncomputable def secondLargestAdjEigenvalue
    (hcard : Fintype.card V ≥ 2) : ℝ :=
  G.adjEigenvalues ⟨1, by omega⟩


end SimpleGraph

namespace BipartiteMatching

open Finset

noncomputable def partialMatchingsOfSize (n : ℕ) (adj : Fin n → Fin n → Bool) (k : ℕ) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact (Finset.univ (α := Finset (Fin n × Fin n))).filter fun m =>
    m.card = k ∧
    (∀ p ∈ m, adj p.1 p.2 = true) ∧
    (m.image Prod.fst).card = m.card ∧
    (m.image Prod.snd).card = m.card

def HasMinDegree (n : ℕ) (adj : Fin n → Fin n → Bool) (d : ℕ) : Prop :=
  (∀ i : Fin n, (Finset.univ.filter (fun j => adj i j = true)).card ≥ d) ∧
  (∀ j : Fin n, (Finset.univ.filter (fun i => adj i j = true)).card ≥ d)


end BipartiteMatching

namespace SpectralExpanders

structure GraphFamily where
  V : ℕ → Type*
  instFintype : ∀ n, Fintype (V n)
  instDecidableEq : ∀ n, DecidableEq (V n)
  G : ∀ n, SimpleGraph (V n)
  instDecidableAdj : ∀ n, DecidableRel (G n).Adj
  d : ℕ
  isRegular : ∀ n, (G n).IsRegularOfDegree d
  card_ge_two : ∀ n, @Fintype.card (V n) (instFintype n) ≥ 2

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

namespace ExpanderDiameter

open Polynomial Matrix Finset BigOperators SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable abbrev diameter {V : Type*} (G : SimpleGraph V) : ℕ := G.diam

end SimpleGraph
