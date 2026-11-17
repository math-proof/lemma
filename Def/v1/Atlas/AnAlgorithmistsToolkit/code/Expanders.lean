/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Expanders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders

@[expose] public section

namespace Expanders

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
