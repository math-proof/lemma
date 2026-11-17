/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/CanonicalPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace CanonicalPaths

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def edgesCut (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e =>
    ∃ v w, e = s(v, w) ∧ v ∈ S ∧ w ∉ S)).card

noncomputable def volume (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, G.degree v

noncomputable def conductanceSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  if min (volume G S) (volume G (Finset.univ \ S)) = 0 then 0
  else (edgesCut G S : ℝ) / (min (volume G S) (volume G (Finset.univ \ S)) : ℝ)

noncomputable def conductance (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf {x : ℝ | ∃ S : Finset V, S.Nonempty ∧ S ≠ Finset.univ ∧ x = conductanceSet G S}

noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (G.degree ·)

def CanonicalPathSystem (G : SimpleGraph V) :=
  (v : V) → (w : V) → G.Walk v w

noncomputable def congestion (G : SimpleGraph V) [DecidableRel G.Adj]
    (paths : CanonicalPathSystem G) (e : Sym2 V) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V =>
    e ∈ (paths p.1 p.2).edges)).card

end CanonicalPaths
