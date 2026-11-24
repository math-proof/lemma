module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
public import Mathlib.Combinatorics.SimpleGraph.Dart


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

def isingFiniteGraphDartSum
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (F : V → V → Real) : Real := by
  classical
  exact ∑ d : G.Dart, F d.fst d.snd

def isingFiniteGraphDartEquiv
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (Σ x, G.neighborSet x) ≃ G.Dart where
  toFun p := ⟨(p.1, p.2.1), p.2.2⟩
  invFun d := ⟨d.fst, ⟨d.snd, d.adj⟩⟩
  left_inv p := by cases p; rfl
  right_inv d := by cases d; rfl


end
end StatMech.Universality
