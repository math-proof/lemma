/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy


namespace StatMech.FrontierA

def embeddingOf_tag_preserving_fiberwise
    {B C S : Type*} (sourceTag : B -> S) (targetTag : C -> S)
    (f : B -> C)
    (htag : ∀ x, targetTag (f x) = sourceTag x)
    (hfiber : ∀ s, Function.Injective fun x : {x : B // sourceTag x = s} =>
      f x.1) : B ↪ C where
  toFun := f
  inj' := by
    intro x y hxy
    have htags : sourceTag x = sourceTag y := by
      rw [← htag x, ← htag y, hxy]
    let xs : {z : B // sourceTag z = sourceTag x} := ⟨x, rfl⟩
    let ys : {z : B // sourceTag z = sourceTag x} := ⟨y, htags.symm⟩
    have hsub : xs = ys := hfiber (sourceTag x) (by
      change f x = f y
      exact hxy)
    exact congrArg Subtype.val hsub


def embeddingOf_taggedFiberwiseMaps
    {B C S : Type*} (sourceTag : B -> S) (targetTag : C -> S)
    (f : S -> B -> C)
    (htag : ∀ s x, sourceTag x = s -> targetTag (f s x) = s)
    (hinj : ∀ s, Function.Injective fun
      x : {x : B // sourceTag x = s} => f s x.1) : B ↪ C := by
  let assembled : B -> C := fun x => f (sourceTag x) x
  apply embeddingOf_tag_preserving_fiberwise
    sourceTag targetTag assembled
  · intro x
    exact htag (sourceTag x) x rfl
  · intro s x y hxy
    have hsub : x = y := hinj s (by
      simpa only [assembled, x.2, y.2] using hxy)
    exact hsub


noncomputable def embeddingOf_taggedFiberwiseCardLE
    {B C S : Type*} [Fintype B] [Fintype C] [DecidableEq S]
    (sourceTag : B -> S) (targetTag : C -> S)
    (hcard : ∀ s,
      Fintype.card {x : B // sourceTag x = s} ≤
        Fintype.card {y : C // targetTag y = s}) : B ↪ C := by
  classical
  let fibreEmbedding : ∀ s,
      {x : B // sourceTag x = s} ↪ {y : C // targetTag y = s} :=
    fun s => Classical.choice (Function.Embedding.nonempty_of_card_le (hcard s))
  by_cases hB : Nonempty B
  · let x : B := Classical.choice hB
    let c : C := (fibreEmbedding (sourceTag x) ⟨x, rfl⟩).1
    let f : S -> B -> C := fun s y =>
      if h : sourceTag y = s then (fibreEmbedding s ⟨y, h⟩).1 else c
    apply embeddingOf_taggedFiberwiseMaps sourceTag targetTag f
    · intro s y hy
      simp only [f, dif_pos hy]
      exact (fibreEmbedding s ⟨y, hy⟩).2
    · intro s y z hyz
      apply (fibreEmbedding s).injective
      apply Subtype.ext
      simpa only [f, dif_pos y.2, dif_pos z.2] using hyz
  · exact ⟨fun x => False.elim (hB ⟨x⟩), fun x => False.elim (hB ⟨x⟩)⟩


def functionWeakComponent {B : Type*} (next : B -> B) (x : B) : Set B :=
  {y | Relation.EqvGen (fun a b => next a = b) x y}

end StatMech.FrontierA
