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
import Def.Combinatorics.DensityHalesJewett.Part13
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhj_exists_structured_tiling {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : ∀ ε : ℝ, 0 < ε → dhjThreshold k ε) :
    ∀ r d : ℕ, 0 < d → ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∃ n : ℕ, ∀ (a : Fin r → Fin k)
        (D : Fin r → Finset (Fin n → Fin (k + 1))),
        (∀ j, dhjInsensitive (a j) (D j)) →
          ∃ C : Finset (Fin n → Fin (k + 1)),
            C ⊆ dhjMeet D ∧ dhjTiled d k C ∧
              dhjDensity (dhjMeet D \ C) ≤ 2 * (r : ℝ) * β := by
  intro r
  induction r with
  | zero =>
      intro d hd β hβ hβle
      refine ⟨d, ?_⟩
      intro a D hD
      have hmeet : dhjMeet D = Finset.univ := by
        ext x
        simp
      have htile : dhjTiled d k
          (Finset.univ : Finset (Fin d → Fin (k + 1))) := by
        have hadd := dhjTiled.add
          (∅ : Finset (Fin d → Fin (k + 1))) (dhjIdentitySubspace d k)
          (dhjTiled.empty : dhjTiled d k
            (∅ : Finset (Fin d → Fin (k + 1))))
          (Finset.disjoint_empty_left _)
        simpa [dhjSubspacePoints_identity] using hadd
      refine ⟨Finset.univ, by simp [hmeet], htile, ?_⟩
      simp [hmeet, dhjDensity_empty]
  | succ r ih =>
      intro d hd β hβ hβle
      obtain ⟨m, hm, hSingle⟩ :=
        dhj_exists_tiling_insensitive_fin hk hd hβ hβle hDHJ
      obtain ⟨n, hOuter⟩ := ih m hm β hβ hβle
      refine ⟨n, ?_⟩
      intro a D hD
      let a₀ : Fin r → Fin k := fun j => a j.castSucc
      let D₀ : Fin r → Finset (Fin n → Fin (k + 1)) := fun j => D j.castSucc
      have hD₀ : ∀ j, dhjInsensitive (a₀ j) (D₀ j) := fun j => hD j.castSucc
      obtain ⟨C, hCsub, hCtile, hCsmall⟩ := hOuter a₀ D₀ hD₀
      let i := a (Fin.last r)
      let E := D (Fin.last r)
      have hE : dhjInsensitive i E := hD (Fin.last r)
      obtain ⟨B, hBsub, hBtile, hBsmall⟩ :=
        dhj_refine_tiled i (hSingle i) E hE hCtile
      have hmeet : dhjMeet D = dhjMeet D₀ ∩ E := by
        simpa [D₀, E] using dhjMeet_succ D
      refine ⟨B, ?_, hBtile, ?_⟩
      · intro x hx
        rw [hmeet]
        have hx' := Finset.mem_inter.mp (hBsub hx)
        exact Finset.mem_inter.mpr ⟨hCsub hx'.1, hx'.2⟩
      · let M := dhjMeet D₀ ∩ E
        let X := M \ C
        let Y := (C ∩ E) \ B
        have hres : dhjMeet D \ B = X ∪ Y := by
          rw [hmeet]
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, X, Y, M]
          constructor
          · rintro ⟨hxM, hxB⟩
            by_cases hxC : x ∈ C
            · exact Or.inr ⟨⟨hxC, hxM.2⟩, hxB⟩
            · exact Or.inl ⟨hxM, hxC⟩
          · rintro (⟨hxM, hxC⟩ | ⟨⟨hxC, hxE'⟩, hxB⟩)
            · refine ⟨hxM, ?_⟩
              intro hxB
              exact hxC (Finset.mem_inter.mp (hBsub hxB)).1
            · exact ⟨⟨hCsub hxC, hxE'⟩, hxB⟩
        have hXY : Disjoint X Y := by
          rw [Finset.disjoint_left]
          intro x hxX hxY
          exact (Finset.mem_sdiff.mp hxX).2
            (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxY).1).1
        have hXsub : X ⊆ dhjMeet D₀ \ C := by
          intro x hx
          have hx' := Finset.mem_sdiff.mp hx
          exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx'.1).1, hx'.2⟩
        have hXsmall : dhjDensity X ≤ 2 * (r : ℝ) * β :=
          (dhjDensity_mono hXsub).trans hCsmall
        have hYsmall : dhjDensity Y ≤ 2 * β := by
          calc
            dhjDensity Y ≤ 2 * β * dhjDensity C := hBsmall
            _ ≤ 2 * β * 1 := by
              exact mul_le_mul_of_nonneg_left (dhjDensity_le_one C) (by positivity)
            _ = 2 * β := by ring
        rw [hres, dhjDensity_union X Y hXY]
        calc
          dhjDensity X + dhjDensity Y ≤ 2 * (r : ℝ) * β + 2 * β :=
            add_le_add hXsmall hYsmall
          _ = 2 * ((r + 1 : ℕ) : ℝ) * β := by
            push_cast
            ring

theorem dhj_inter_subspacePoints {k m : ℕ} {I : Type*}
    [DecidableEq (I → Fin (k + 1))]
    (A : Finset (I → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    A ∩ dhjSubspacePoints V =
      (dhjPullback V A).map ⟨V, dhjSubspace_apply_injective V⟩ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := (dhj_mem_subspacePoints V x).mp
      (Finset.mem_inter.mp hx).2
    exact Finset.mem_map.mpr
      ⟨z, (dhj_mem_pullback V A z).mpr (Finset.mem_inter.mp hx).1, rfl⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_inter.mpr
      ⟨(dhj_mem_pullback V A z).mp hz,
        (dhj_mem_subspacePoints V (V z)).mpr ⟨z, rfl⟩⟩

theorem dhjDensity_inter_subspacePoints {k m : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))] [DecidableEq (I → Fin (k + 1))]
    (A : Finset (I → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) I) :
    dhjDensity (A ∩ dhjSubspacePoints V) =
      dhjDensityOn A V * dhjDensity (dhjSubspacePoints V) := by
  rw [dhj_inter_subspacePoints A V, dhjDensity_map_subspace]
  rfl

theorem dhjTiled.exists_densityOn_ge {k d : ℕ} {I : Type*}
    [Fintype (I → Fin (k + 1))]
    [DecidableEq (I → Fin (k + 1))]
    {C : Finset (I → Fin (k + 1))} (hC : dhjTiled d k C)
    (A : Finset (I → Fin (k + 1))) {q : ℝ} (hCne : C.Nonempty)
    (havg : q * dhjDensity C ≤ dhjDensity (A ∩ C)) :
    ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) I,
      dhjSubspacePoints V ⊆ C ∧ q ≤ dhjDensityOn A V := by
  induction hC with
  | empty => simp at hCne
  | add C V hCtiled hdis ih =>
      by_cases hV : q ≤ dhjDensityOn A V
      · refine ⟨V, ?_, hV⟩
        exact Finset.subset_union_right
      · have hAdis : Disjoint (A ∩ C) (A ∩ dhjSubspacePoints V) := by
          rw [Finset.disjoint_left]
          intro x hxC hxV
          exact (Finset.disjoint_left.mp hdis)
            (Finset.mem_inter.mp hxC).2 (Finset.mem_inter.mp hxV).2
        have hAunion : A ∩ (C ∪ dhjSubspacePoints V) =
            (A ∩ C) ∪ (A ∩ dhjSubspacePoints V) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          aesop
        have htotal : q *
              (dhjDensity C + dhjDensity (dhjSubspacePoints V)) ≤
            dhjDensity (A ∩ C) +
              dhjDensity (A ∩ dhjSubspacePoints V) := by
          rw [← dhjDensity_union C (dhjSubspacePoints V) hdis,
            ← dhjDensity_union (A ∩ C) (A ∩ dhjSubspacePoints V) hAdis,
            ← hAunion]
          exact havg
        have hVpos : 0 < dhjDensity (dhjSubspacePoints V) := by
          rw [dhjDensity_subspacePoints]
          positivity
        have hVsmall : dhjDensity (A ∩ dhjSubspacePoints V) <
            q * dhjDensity (dhjSubspacePoints V) := by
          rw [dhjDensity_inter_subspacePoints A V]
          exact mul_lt_mul_of_pos_right (lt_of_not_ge hV) hVpos
        have hprev : q * dhjDensity C < dhjDensity (A ∩ C) := by
          nlinarith
        have hCne' : C.Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty.mp h, dhjDensity_empty] at hprev
          simp [dhjDensity_empty] at hprev
        obtain ⟨W, hWsub, hWden⟩ := ih hCne' hprev.le
        exact ⟨W, hWsub.trans Finset.subset_union_left, hWden⟩

end MathlibExt.Combinatorics.DensityHalesJewettWanted
