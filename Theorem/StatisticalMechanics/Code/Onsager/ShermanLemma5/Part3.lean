/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma5.Part2


namespace StatMech.Onsager

open Matrix BigOperators


theorem ons_mir_val {n : ℕ} [NeZero n] {l m k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    (ons_mir l m k).val = l.val + m.val - k.val := by
  have hml : m.val < n := m.isLt
  have hlk' : l.val ≤ k.val := hlk
  have hkm' : k.val ≤ m.val := hkm
  unfold ons_mir
  simp only []
  omega


theorem ons_mir_mem {n : ℕ} [NeZero n] {l m k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    l ≤ ons_mir l m k ∧ ons_mir l m k ≤ m := by
  have hv := ons_mir_val hlk hkm
  have hlk' : l.val ≤ k.val := hlk
  have hkm' : k.val ≤ m.val := hkm
  constructor
  · show l.val ≤ (ons_mir l m k).val; omega
  · show (ons_mir l m k).val ≤ m.val; omega


theorem ons_mir_mir {n : ℕ} [NeZero n] {l m k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    ons_mir l m (ons_mir l m k) = k := by
  obtain ⟨h1, h2⟩ := ons_mir_mem hlk hkm
  have hv := ons_mir_val hlk hkm
  have hv2 := ons_mir_val h1 h2
  have hlk' : l.val ≤ k.val := hlk
  have hkm' : k.val ≤ m.val := hkm
  have hkn : k.val < n := k.isLt
  apply Fin.ext
  rw [hv2, hv]
  omega


theorem ons_mir_l {n : ℕ} [NeZero n] {l m : Fin n} (hlm : l ≤ m) :
    ons_mir l m l = m := by
  have hv := ons_mir_val (le_refl l) hlm
  apply Fin.ext; rw [hv]; have : l.val ≤ m.val := hlm; omega


theorem ons_mir_m {n : ℕ} [NeZero n] {l m : Fin n} (hlm : l ≤ m) :
    ons_mir l m m = l := by
  have hv := ons_mir_val hlm (le_refl m)
  apply Fin.ext; rw [hv]; have : l.val ≤ m.val := hlm; omega


end StatMech.Onsager
