/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part4


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


def bc19_reindex {A B : Set V} {ι κ : Type*} (E : κ ≃ ι)
    (F : bc16_DisjointPathFamily G A B ι) : bc16_DisjointPathFamily G A B κ where
  a := fun i => F.a (E i)
  b := fun i => F.b (E i)
  p := fun i => F.p (E i)
  ha := fun i => F.ha (E i)
  hb := fun i => F.hb (E i)
  hp := fun i => F.hp (E i)
  hdisj := by
    intro i j hij z hzi hzj
    exact F.hdisj (fun h => hij (E.injective h)) hzi hzj


def bc19_directSum {A B Y : Set V} {x y : V} {m : ℕ}
    (hxy : G.Adj x y) (f : Fin m → V) (hf : ∀ i, f i ∈ Y)
    (hinj : Function.Injective f)
    (hxY : x ∉ Y) (hyY : y ∉ Y)
    (hxA : x ∈ A) (hyB : y ∈ B) (hYA : Y ⊆ A) (hYB : Y ⊆ B) :
    bc16_DisjointPathFamily G A B (Sum (Fin m) Unit) where
  a := Sum.elim f (fun _ => x)
  b := Sum.elim f (fun _ => y)
  p := fun i => match i with
    | Sum.inl j => (Walk.nil : G.Walk (f j) (f j))
    | Sum.inr _ => Walk.cons hxy Walk.nil
  ha := by rintro (j | _); exacts [hYA (hf j), hxA]
  hb := by rintro (j | _); exacts [hYB (hf j), hyB]
  hp := by rintro (j | _); exacts [Walk.IsPath.nil, Walk.IsPath.of_adj hxy]
  hdisj := by
    rintro (i | _) (j | _) hij z hzi hzj <;> simp only at hzi hzj
    · have h1 := Walk.mem_support_nil_iff.mp hzi
      have h2 := Walk.mem_support_nil_iff.mp hzj
      exact hij (by rw [Sum.inl.injEq]; exact hinj (h1.symm.trans h2))
    · have h1 := Walk.mem_support_nil_iff.mp hzi
      rw [Sum.elim_inl] at h1
      simp only [Walk.support_cons, Walk.support_nil, Sum.elim_inr, List.mem_cons,
        List.not_mem_nil, or_false] at hzj
      rcases hzj with h | h
      · exact hxY (by rw [← h, h1]; exact hf i)
      · exact hyY (by rw [← h, h1]; exact hf i)
    · have h2 := Walk.mem_support_nil_iff.mp hzj
      rw [Sum.elim_inl] at h2
      simp only [Walk.support_cons, Walk.support_nil, Sum.elim_inr, List.mem_cons,
        List.not_mem_nil, or_false] at hzi
      rcases hzi with h | h
      · exact hxY (by rw [← h, h2]; exact hf j)
      · exact hyY (by rw [← h, h2]; exact hf j)
    · exact hij rfl


noncomputable def bc19_sumEquiv (m : ℕ) : (Sum (Fin m) Unit) ≃ Fin (m + 1) :=
  Fintype.equivFinOfCardEq (by simp)


end StatMech.Walls
