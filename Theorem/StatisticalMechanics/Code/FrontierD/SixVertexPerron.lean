/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
open Finset Matrix


namespace StatMech.FrontierD

theorem pairwise_flatMap_pairs {ι α : Type*} [Preorder α]
    (f g : ι → α) {l : List ι} (hsame : ∀ i ∈ l, f i ≤ g i)
    (hcross : l.Pairwise fun i j => g i ≤ f j) :
    (l.flatMap fun i => [f i, g i]).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.pairwise_cons] at hcross
      change List.Pairwise (· ≤ ·) (f a :: g a :: (l.flatMap fun i => [f i, g i]))
      rw [List.pairwise_cons_cons_iff_of_trans]
      refine ⟨hsame a (by simp), ?_⟩
      rw [List.pairwise_cons]
      refine ⟨?_, ih (fun i hi => hsame i (by simp [hi])) hcross.2⟩
      intro z hz
      simp only [List.mem_flatMap] at hz
      obtain ⟨i, hi, hz⟩ := hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hcross.1 i hi
      · exact (hcross.1 i hi).trans (hsame i (by simp [hi]))

theorem zip_map_same {ι α β : Type*} (l : List ι) (f : ι → α) (g : ι → β) :
    (l.map f).zip (l.map g) = l.map fun i => (f i, g i) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]


end StatMech.FrontierD
