/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem lipschitzOnWith_of_open_local_on_convex
    (f : Complex -> Complex) (s : Set Complex) (C : NNReal)
    (hs : Convex Real s)
    (hlocal : ∀ z ∈ s, ∃ u : Set Complex,
      IsOpen u ∧ z ∈ u ∧ LipschitzOnWith C f (u ∩ s)) :
    LipschitzOnWith C f s := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let g : Set.Icc (0 : Real) 1 -> Complex := fun t =>
    AffineMap.lineMap x y (t : Real)
  have hgmem (t : Set.Icc (0 : Real) 1) : g t ∈ s := by
    exact hs.lineMap_mem hx hy t.property
  choose u huOpen hgu hLip using fun t => hlocal (g t) (hgmem t)
  let c : Set.Icc (0 : Real) 1 -> Set (Set.Icc (0 : Real) 1) :=
    fun t => g ⁻¹' u t
  have hcOpen : forall t, IsOpen (c t) := by
    intro t
    exact (huOpen t).preimage (by
      dsimp only [g]
      fun_prop)
  have hcCover : Set.univ ⊆ ⋃ t, c t := by
    intro t _ht
    exact Set.mem_iUnion.2 ⟨t, hgu t⟩
  obtain ⟨T, hT0, hTmono, ⟨N, hTN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  have hstep (a : Nat) :
      dist (f (g (T a))) (f (g (T (a + 1)))) <=
        (C : Real) * (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
          ((T a : Set.Icc (0 : Real) 1) : Real)) * dist x y := by
    obtain ⟨q, hq⟩ := hsub a
    have hTa : T a ∈ c q := hq (Set.left_mem_Icc.2 (hTmono (Nat.le_succ a)))
    have hTa1 : T (a + 1) ∈ c q :=
      hq (Set.right_mem_Icc.2 (hTmono (Nat.le_succ a)))
    have hbound := LipschitzOnWith.dist_le_mul (hLip q)
      (g (T a)) ⟨hTa, hgmem (T a)⟩
      (g (T (a + 1))) ⟨hTa1, hgmem (T (a + 1))⟩
    have hcoeff :
        0 <= ((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
          ((T a : Set.Icc (0 : Real) 1) : Real) := by
      exact sub_nonneg.mpr (hTmono (Nat.le_succ a))
    calc
      dist (f (g (T a))) (f (g (T (a + 1)))) <=
          (C : Real) * dist (g (T a)) (g (T (a + 1))) := hbound
      _ = (C : Real) *
          (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
            ((T a : Set.Icc (0 : Real) 1) : Real)) * dist x y := by
        rw [show dist (g (T a)) (g (T (a + 1))) =
            dist ((T a : Set.Icc (0 : Real) 1) : Real)
              ((T (a + 1) : Set.Icc (0 : Real) 1) : Real) * dist x y by
          exact dist_lineMap_lineMap (𝕜 := Real) x y _ _]
        rw [Real.dist_eq, abs_of_nonpos
          (by linarith [hcoeff] :
            ((T a : Set.Icc (0 : Real) 1) : Real) -
              ((T (a + 1) : Set.Icc (0 : Real) 1) : Real) <= 0)]
        ring
  have hpath := dist_le_range_sum_dist (fun a => f (g (T a))) N
  have hsum :
      (∑ a ∈ Finset.range N,
        (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
          ((T a : Set.Icc (0 : Real) 1) : Real))) = 1 := by
    have htel :
        (∑ a ∈ Finset.range N,
          (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
            ((T a : Set.Icc (0 : Real) 1) : Real))) =
          ((T N : Set.Icc (0 : Real) 1) : Real) -
            ((T 0 : Set.Icc (0 : Real) 1) : Real) := by
      simpa only using
        (Finset.sum_range_sub (fun a => ((T a : Set.Icc (0 : Real) 1) : Real)) N)
    rw [htel]
    rw [hTN N (le_refl N), hT0]
    norm_num
  calc
    dist (f x) (f y) = dist (f (g (T 0))) (f (g (T N))) := by
      rw [hT0, hTN N (le_refl N)]
      simp [g]
    _ <= ∑ a ∈ Finset.range N,
        dist (f (g (T a))) (f (g (T (a + 1)))) := hpath
    _ <= ∑ a ∈ Finset.range N,
        ((C : Real) *
          (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
            ((T a : Set.Icc (0 : Real) 1) : Real)) * dist x y) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hstep a
    _ = (C : Real) * dist x y := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
      ring


theorem complexBilinearCell_right_eq_left
    (a00 a10 a01 a11 b10 b11 : Complex) (y : Real) :
    complexBilinearCell a00 a10 a01 a11 1 y =
      complexBilinearCell a10 b10 a11 b11 0 y := by
  unfold complexBilinearCell
  push_cast
  ring


theorem complexBilinearCell_top_eq_bottom
    (a00 a10 a01 a11 b01 b11 : Complex) (x : Real) :
    complexBilinearCell a00 a10 a01 a11 x 1 =
      complexBilinearCell a01 a11 b01 b11 x 0 := by
  unfold complexBilinearCell
  push_cast
  ring


theorem complexBilinearCell_horizontalAdjacent_norm_sub_le
    (a00 a10 a01 a11 b10 b11 : Complex)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom : norm (a10 - a00) <= D)
    (haTop : norm (a11 - a01) <= D)
    (haLeft : norm (a01 - a00) <= D)
    (haRight : norm (a11 - a10) <= D)
    (hbBottom : norm (b10 - a10) <= D)
    (hbTop : norm (b11 - a11) <= D)
    (hbRight : norm (b11 - b10) <= D) :
    norm (complexBilinearCell a00 a10 a01 a11 x y -
      complexBilinearCell a10 b10 a11 b11 x' y') <=
        D * ((1 - x) + x' + |y - y'|) := by
  let shared := complexBilinearCell a00 a10 a01 a11 1 y
  have hleft :
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) <=
        D * (1 - x) := by
    have h := complexBilinearCell_norm_sub_le
      a00 a10 a01 a11 x 1 y y D (by norm_num) (by norm_num)
      hy0 hy1 haBottom haTop haLeft haRight
    simpa [shared, abs_of_nonpos (by linarith : x - 1 <= 0)] using h
  have hshared :
      shared = complexBilinearCell a10 b10 a11 b11 0 y := by
    exact complexBilinearCell_right_eq_left _ _ _ _ _ _ _
  have hright :
      norm (shared - complexBilinearCell a10 b10 a11 b11 x' y') <=
        D * (x' + |y - y'|) := by
    rw [hshared]
    have h := complexBilinearCell_norm_sub_le
      a10 b10 a11 b11 0 x' y y' D hx0' hx1' hy0 hy1
      hbBottom hbTop haRight hbRight
    simpa [abs_of_nonneg hx0'] using h
  calc
    norm (complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a10 b10 a11 b11 x' y') <=
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) +
        norm (shared - complexBilinearCell a10 b10 a11 b11 x' y') := by
          rw [show complexBilinearCell a00 a10 a01 a11 x y -
              complexBilinearCell a10 b10 a11 b11 x' y' =
            (complexBilinearCell a00 a10 a01 a11 x y - shared) +
              (shared - complexBilinearCell a10 b10 a11 b11 x' y') by ring]
          exact norm_add_le _ _
    _ <= D * (1 - x) + D * (x' + |y - y'|) := add_le_add hleft hright
    _ = D * ((1 - x) + x' + |y - y'|) := by ring


theorem complexBilinearCell_verticalAdjacent_norm_sub_le
    (a00 a10 a01 a11 b01 b11 : Complex)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom : norm (a10 - a00) <= D)
    (haTop : norm (a11 - a01) <= D)
    (haLeft : norm (a01 - a00) <= D)
    (haRight : norm (a11 - a10) <= D)
    (hbTop : norm (b11 - b01) <= D)
    (hbLeft : norm (b01 - a01) <= D)
    (hbRight : norm (b11 - a11) <= D) :
    norm (complexBilinearCell a00 a10 a01 a11 x y -
      complexBilinearCell a01 a11 b01 b11 x' y') <=
        D * (|x - x'| + (1 - y) + y') := by
  let shared := complexBilinearCell a00 a10 a01 a11 x 1
  have hlower :
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) <=
        D * (1 - y) := by
    have h := complexBilinearCell_norm_sub_le
      a00 a10 a01 a11 x x y 1 D hx0 hx1 hy0 hy1
      haBottom haTop haLeft haRight
    simpa [shared, abs_of_nonpos (by linarith : y - 1 <= 0)] using h
  have hshared :
      shared = complexBilinearCell a01 a11 b01 b11 x 0 := by
    exact complexBilinearCell_top_eq_bottom _ _ _ _ _ _ _
  have hupper :
      norm (shared - complexBilinearCell a01 a11 b01 b11 x' y') <=
        D * (|x - x'| + y') := by
    rw [hshared]
    have h := complexBilinearCell_norm_sub_le
      a01 a11 b01 b11 x x' 0 y' D hx0' hx1' (by norm_num) (by norm_num)
      haTop hbTop hbLeft hbRight
    simpa [abs_of_nonneg hy0'] using h
  calc
    norm (complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a01 a11 b01 b11 x' y') <=
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) +
        norm (shared - complexBilinearCell a01 a11 b01 b11 x' y') := by
          rw [show complexBilinearCell a00 a10 a01 a11 x y -
              complexBilinearCell a01 a11 b01 b11 x' y' =
            (complexBilinearCell a00 a10 a01 a11 x y - shared) +
              (shared - complexBilinearCell a01 a11 b01 b11 x' y') by ring]
          exact norm_add_le _ _
    _ <= D * (1 - y) + D * (|x - x'| + y') := add_le_add hlower hupper
    _ = D * (|x - x'| + (1 - y) + y') := by ring


end
end StatMech.Universality
