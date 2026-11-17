/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Structure.v1.Atlas.BooleanFunctions.code.EdgeExpansion

@[expose] public section

namespace BooleanAnalysis

noncomputable def WeightedRegularGraph.edgeExpansion {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedRegularGraph V) (S : Finset V) : ℝ :=
  if S = ∅ then 0
  else
    (∑ x ∈ S, ∑ y ∈ Finset.univ.filter (fun v => v ∉ S), G.weight x y) /
      (G.degree * S.card)

def flip (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

noncomputable def edgeExpansion (n : ℕ) (A : Finset (Fin n → Bool)) : ℝ :=
  if n = 0 ∨ A = ∅ then 0
  else
    ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      p.1 ∈ A ∧ flip p.1 p.2 ∉ A)).card : ℝ) / (n * A.card : ℝ)

noncomputable def edgeBoundaryMeasure (n : ℕ) (A : Finset (Fin n → Bool)) : ℝ :=
  if n = 0 then 0
  else
    ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).card : ℝ) / (n * 2 ^ n : ℝ)

end BooleanAnalysis
