/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part3


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


@[simp] theorem kwListDirection_ofFn (word : List (Fin 4)) :
    List.ofFn (kwListDirection word) = word := List.ofFn_get word

theorem kwListDirection_pos_eq_prefixPosition
    (word : List (Fin 4)) [NeZero word.length]
    (k : Fin word.length) :
    pos (kwListDirection word) k =
      (kwPrefixPositions word).get
        ⟨k.val, by simpa using k.isLt⟩ := by
  rw [kwPrefixPositions_get]
  unfold pos
  have hsum := List.sum_take_ofFn
    (f := fun i : Fin word.length ↦ stepOf (kwListDirection word i)) k.val
  have hofn : List.ofFn
      (fun i : Fin word.length ↦ stepOf (kwListDirection word i)) =
      word.map stepOf := by
    change List.ofFn (stepOf ∘ kwListDirection word) = word.map stepOf
    rw [← List.map_ofFn, kwListDirection_ofFn]
  rw [hofn] at hsum
  simpa only [Fin.mk_lt_mk, List.map_take] using hsum.symm

theorem kwListDirection_pos_injective_of_prefixPositions_nodup
    (word : List (Fin 4)) [NeZero word.length]
    (h : (kwPrefixPositions word).Nodup) :
    Function.Injective (pos (kwListDirection word)) := by
  intro i j hij
  have hget : (kwPrefixPositions word).get
      ⟨i.val, by simpa using i.isLt⟩ =
      (kwPrefixPositions word).get
      ⟨j.val, by simpa using j.isLt⟩ := by
    rw [← kwListDirection_pos_eq_prefixPosition,
      ← kwListDirection_pos_eq_prefixPosition]
    exact hij
  have hfin := h.injective_get hget
  apply Fin.ext
  exact congrArg
    (fun q : Fin (kwPrefixPositions word).length ↦ q.val) hfin

theorem kwPrefixPositions_replicate (d : Fin 4) (N : ℕ) :
    kwPrefixPositions (List.replicate N d) =
      (List.range N).map (fun k ↦ k • stepOf d) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [List.replicate_succ, kwPrefixPositions_cons, ih,
        List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp
      · rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        simp only [Function.comp_apply]
        rw [succ_nsmul]
        abel

theorem kwPrefixPositions_replicate_nodup (d : Fin 4) (N : ℕ) :
    (kwPrefixPositions (List.replicate N d)).Nodup := by
  rw [kwPrefixPositions_replicate]
  apply (List.nodup_range (n := N)).map
  intro a b hab
  fin_cases d <;> simp [stepOf, Prod.ext_iff] at hab <;> omega

theorem kwPrefixPositions_integralAxisWord_nodup
    {v : ℤ × ℤ} (haxis : v.1 = 0 ∨ v.2 = 0) :
    (kwPrefixPositions (kwIntegralAxisWord v)).Nodup := by
  rcases haxis with hx | hy
  · simp [kwIntegralAxisWord, hx,
      kwPrefixPositions_replicate_nodup]
  · simp [kwIntegralAxisWord, hy,
      kwPrefixPositions_replicate_nodup]

@[simp] theorem kwIntComplex_zero : kwIntComplex 0 = 0 := by
  simp [kwIntComplex]

theorem kwIntComplex_add (p q : ℤ × ℤ) :
    kwIntComplex (p + q) = kwIntComplex p + kwIntComplex q := by
  apply Complex.ext <;> simp [kwIntComplex]

theorem kwIntComplex_nsmul_stepOf (d : Fin 4) (k : ℕ) :
    kwIntComplex (k • stepOf d) =
      (k : ℝ) * kwRectilinearVector d := by
  fin_cases d <;>
    apply Complex.ext <;>
    simp [kwIntComplex, kwRectilinearVector, stepOf]

theorem kw_replicate_prefix_mem_halfOpen
    (start : ℂ) (d : Fin 4) (N : ℕ) {q : ℤ × ℤ}
    (hq : q ∈ kwPrefixPositions (List.replicate N d)) :
    start + kwIntComplex q = start ∨
      Sbtw ℝ start (start + kwIntComplex q)
        (start + kwIntComplex (N • stepOf d)) := by
  rw [kwPrefixPositions_replicate, List.mem_map] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  have hkN : k < N := List.mem_range.mp hk
  by_cases hk0 : k = 0
  · subst k
    simp
  · right
    have hN : 0 < N := Nat.pos_of_ne_zero (by omega)
    have hvec : (N : ℝ) * kwRectilinearVector d ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hN.ne') (kwRectilinearVector_ne_zero d)
    have hline : (k : ℝ) * kwRectilinearVector d =
        AffineMap.lineMap 0 ((N : ℝ) * kwRectilinearVector d)
          ((k : ℝ) / N) := by
      rw [AffineMap.lineMap_apply_module]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
          zero_mul, sub_zero] <;>
        field_simp [hNr] <;> ring
    have hs : Sbtw ℝ (0 : ℂ) ((k : ℝ) * kwRectilinearVector d)
        ((N : ℝ) * kwRectilinearVector d) := by
      rw [hline]
      apply sbtw_lineMap_iff.mpr
      refine ⟨hvec.symm, div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk0) ?_, ?_⟩
      · exact_mod_cast hN
      · exact (div_lt_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hkN)
    simpa only [kwIntComplex_nsmul_stepOf, zero_add, add_zero] using
      hs.const_add start

theorem integralAxisWord_eq_replicate_of_axis
    {v : ℤ × ℤ} (haxis : v.1 = 0 ∨ v.2 = 0) :
    ∃ (d : Fin 4) (N : ℕ), kwIntegralAxisWord v = List.replicate N d ∧
      N • stepOf d = v := by
  rcases haxis with hx | hy
  · refine ⟨kwVerticalIntDirection v.2, v.2.natAbs, ?_, ?_⟩
    · simp [kwIntegralAxisWord, hx]
    · have hsum := sum_replicate_verticalDirection v.2
      calc
        v.2.natAbs • stepOf (kwVerticalIntDirection v.2) = (0, v.2) := by
          simpa only [List.sum_replicate] using hsum
        _ = v := Prod.ext hx.symm rfl
  · refine ⟨kwHorizontalIntDirection v.1, v.1.natAbs, ?_, ?_⟩
    · simp [kwIntegralAxisWord, hy]
    · have hsum := sum_replicate_horizontalDirection v.1
      calc
        v.1.natAbs • stepOf (kwHorizontalIntDirection v.1) = (v.1, 0) := by
          simpa only [List.sum_replicate] using hsum
        _ = v := Prod.ext rfl hy.symm


end StatMech.FrontierA
