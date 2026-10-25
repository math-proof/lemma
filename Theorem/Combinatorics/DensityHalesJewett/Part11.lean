/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Def.Combinatorics.DensityHalesJewett.Part12
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhjSubspacePoints_comp {k m d : ℕ} {I : Type*}
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    (W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)) :
    (dhjSubspacePoints W).map ⟨V, dhjSubspace_apply_injective V⟩ =
      dhjSubspacePoints (V.comp W) := by
  classical
  ext x
  simp [dhjSubspacePoints, Combinatorics.Subspace.comp_apply]

theorem dhjTiled.map_subspace {k m d : ℕ} {I : Type*}
    [DecidableEq (Fin m → Fin (k + 1))]
    [DecidableEq (I → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    {C : Finset (Fin m → Fin (k + 1))} (hC : dhjTiled d k C) :
    dhjTiled d k (C.map ⟨V, dhjSubspace_apply_injective V⟩) := by
  induction hC with
  | empty => simpa using (dhjTiled.empty :
      dhjTiled d k (∅ : Finset (I → Fin (k + 1))))
  | add C W hC hdis ih =>
      have hdis' : Disjoint
          (C.map ⟨V, dhjSubspace_apply_injective V⟩)
          (dhjSubspacePoints (V.comp W)) := by
        rw [← dhjSubspacePoints_comp V W]
        exact (Finset.disjoint_map _).mpr hdis
      have hadd := dhjTiled.add
        (C.map ⟨V, dhjSubspace_apply_injective V⟩) (V.comp W) ih hdis'
      rw [Finset.map_union, dhjSubspacePoints_comp V W]
      exact hadd

theorem dhjDensity_map_subspace {k m : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I)
    (A : Finset (Fin m → Fin (k + 1))) :
    dhjDensity (A.map ⟨V, dhjSubspace_apply_injective V⟩) =
      dhjDensity A * dhjDensity (dhjSubspacePoints V) := by
  rw [dhjDensity, dhjDensity, dhjDensity_subspacePoints]
  simp only [Finset.card_map, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hbase : (0 : ℝ) < (k + 1 : ℕ) ^ m := by positivity
  field_simp

theorem dhj_refine_one_tile {k m d : ℕ} {I : Type*}
    [Fintype I] [Fintype (I → Fin (k + 1))]
    (i : Fin k) {β : ℝ}
    (hSingle : ∀ (D : Finset (Fin m → Fin (k + 1))),
      dhjInsensitive i D →
        ∃ C : Finset (Fin m → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k C ∧ dhjDensity (D \ C) < 2 * β)
    (E : Finset (I → Fin (k + 1))) (hE : dhjInsensitive i E)
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    ∃ B : Finset (I → Fin (k + 1)),
      B ⊆ dhjSubspacePoints V ∩ E ∧ dhjTiled d k B ∧
        dhjDensity ((dhjSubspacePoints V ∩ E) \ B) ≤
          2 * β * dhjDensity (dhjSubspacePoints V) := by
  classical
  let EV := dhjPullback V E
  have hEV : dhjInsensitive i EV := hE.pullback i E V
  obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hSingle EV hEV
  let B := C.map ⟨V, dhjSubspace_apply_injective V⟩
  refine ⟨B, ?_, hCtile.map_subspace V, ?_⟩
  · intro x hx
    obtain ⟨z, hzC, rfl⟩ := Finset.mem_map.mp hx
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩
    · exact (dhj_mem_pullback V E z).mp (hCsub hzC)
  · have hres : (dhjSubspacePoints V ∩ E) \ B =
        (EV \ C).map ⟨V, dhjSubspace_apply_injective V⟩ := by
      ext x
      constructor
      · intro hx
        have hx' := Finset.mem_sdiff.mp hx
        obtain ⟨z, hz⟩ := (dhj_mem_subspacePoints V x).mp
          (Finset.mem_inter.mp hx'.1).1
        subst x
        apply Finset.mem_map.mpr
        refine ⟨z, ?_, rfl⟩
        rw [Finset.mem_sdiff]
        refine ⟨(dhj_mem_pullback V E z).mpr (Finset.mem_inter.mp hx'.1).2, ?_⟩
        intro hzC
        exact hx'.2 (Finset.mem_map.mpr ⟨z, hzC, rfl⟩)
      · intro hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
        have hz' := Finset.mem_sdiff.mp hz
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_inter.mpr ⟨?_, (dhj_mem_pullback V E z).mp hz'.1⟩, ?_⟩
        · exact (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩
        · intro hzB
          obtain ⟨z', hz'C, hz'eq⟩ := Finset.mem_map.mp hzB
          exact hz'.2 ((dhjSubspace_apply_injective V hz'eq) ▸ hz'C)
    rw [hres, dhjDensity_map_subspace]
    have hpos : 0 < dhjDensity (dhjSubspacePoints V) := by
      rw [dhjDensity_subspacePoints]
      positivity
    exact (mul_lt_mul_of_pos_right hCsmall hpos).le

theorem dhj_refine_tiled {k m d : ℕ} {I : Type*}
    [Fintype I] [Fintype (I → Fin (k + 1))]
    (i : Fin k) {β : ℝ}
    (hSingle : ∀ (D : Finset (Fin m → Fin (k + 1))),
      dhjInsensitive i D →
        ∃ C : Finset (Fin m → Fin (k + 1)),
          C ⊆ D ∧ dhjTiled d k C ∧ dhjDensity (D \ C) < 2 * β)
    (E : Finset (I → Fin (k + 1))) (hE : dhjInsensitive i E)
    {C : Finset (I → Fin (k + 1))} (hC : dhjTiled m k C) :
    ∃ B : Finset (I → Fin (k + 1)),
      B ⊆ C ∩ E ∧ dhjTiled d k B ∧
        dhjDensity ((C ∩ E) \ B) ≤ 2 * β * dhjDensity C := by
  induction hC with
  | empty =>
      refine ⟨∅, by simp, dhjTiled.empty, ?_⟩
      simp [dhjDensity_empty]
  | add C V hCtiled hdis ih =>
      obtain ⟨B₀, hB₀sub, hB₀tile, hB₀small⟩ := ih
      obtain ⟨Bᵥ, hBᵥsub, hBᵥtile, hBᵥsmall⟩ :=
        dhj_refine_one_tile i hSingle E hE V
      have hBdis : Disjoint B₀ Bᵥ := by
        rw [Finset.disjoint_left]
        intro x hx₀ hxᵥ
        exact (Finset.disjoint_left.mp hdis)
          (Finset.mem_inter.mp (hB₀sub hx₀)).1
          (Finset.mem_inter.mp (hBᵥsub hxᵥ)).1
      refine ⟨B₀ ∪ Bᵥ, ?_, dhjTiled_union hB₀tile hBᵥtile hBdis, ?_⟩
      · intro x hx
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hx with hx₀ | hxᵥ
          · have hx' := Finset.mem_inter.mp (hB₀sub hx₀)
            exact Finset.mem_union_left _ hx'.1
          · have hx' := Finset.mem_inter.mp (hBᵥsub hxᵥ)
            exact Finset.mem_union_right _ hx'.1
        · rcases Finset.mem_union.mp hx with hx₀ | hxᵥ
          · exact (Finset.mem_inter.mp (hB₀sub hx₀)).2
          · exact (Finset.mem_inter.mp (hBᵥsub hxᵥ)).2
      · let R₀ := (C ∩ E) \ B₀
        let Rᵥ := (dhjSubspacePoints V ∩ E) \ Bᵥ
        have hres : ((C ∪ dhjSubspacePoints V) ∩ E) \ (B₀ ∪ Bᵥ) = R₀ ∪ Rᵥ := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union,
            not_or, R₀, Rᵥ]
          constructor
          · rintro ⟨⟨hxC | hxV, hxE⟩, hxB₀, hxBᵥ⟩
            · exact Or.inl ⟨⟨hxC, hxE⟩, hxB₀⟩
            · exact Or.inr ⟨⟨hxV, hxE⟩, hxBᵥ⟩
          · rintro (⟨⟨hxC, hxE⟩, hxB₀⟩ | ⟨⟨hxV, hxE⟩, hxBᵥ⟩)
            · refine ⟨⟨Or.inl hxC, hxE⟩, hxB₀, ?_⟩
              intro hxBᵥ
              exact (Finset.disjoint_left.mp hdis) hxC
                (Finset.mem_inter.mp (hBᵥsub hxBᵥ)).1
            · refine ⟨⟨Or.inr hxV, hxE⟩, ?_, hxBᵥ⟩
              intro hxB₀
              exact (Finset.disjoint_left.mp hdis)
                (Finset.mem_inter.mp (hB₀sub hxB₀)).1 hxV
        have hRdis : Disjoint R₀ Rᵥ := by
          rw [Finset.disjoint_left]
          intro x hx₀ hxᵥ
          exact (Finset.disjoint_left.mp hdis)
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx₀).1).1
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxᵥ).1).1
        rw [hres, dhjDensity_union R₀ Rᵥ hRdis,
          dhjDensity_union C (dhjSubspacePoints V) hdis]
        calc
          dhjDensity R₀ + dhjDensity Rᵥ ≤
              2 * β * dhjDensity C +
                2 * β * dhjDensity (dhjSubspacePoints V) :=
            add_le_add hB₀small hBᵥsmall
          _ = 2 * β *
              (dhjDensity C + dhjDensity (dhjSubspacePoints V)) := by ring

end MathlibExt.Combinatorics.DensityHalesJewettWanted
