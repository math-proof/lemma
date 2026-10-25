/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.DirectedInverseSystem
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Theorem.v1.Atlas.NumberTheoryI.code.InverseLimits.Part2


noncomputable section

open Set

def InvLim {ι : Type*} [Preorder ι] (X : ι → Type*) (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i) :
    Set (∀ i, X i) :=
  { x | ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i }

noncomputable def adicComplete_ringEquiv_adicCompletion (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] : R ≃+* AdicCompletion I R :=
  RingEquiv.ofBijective (algebraMap R (AdicCompletion I R))
    (AdicCompletion.of_bijective I R)

noncomputable def dvr_ringEquiv_adicCompletion (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    R ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R :=
  adicComplete_ringEquiv_adicCompletion R (IsLocalRing.maximalIdeal R)

section AdicCompletionTopology

noncomputable def padicIntToProd : ℤ_[p] → (∀ n : ℕ, ZMod (p ^ n)) :=
  fun z n => PadicInt.toZModPow n z

def padicInvLimSubring : Subring (∀ n : ℕ, ZMod (p ^ n)) where
  carrier := { x | ∀ (m n : ℕ) (h : m ≤ n),
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (x n) = x m }
  mul_mem' := by
    intro a b ha hb m n h
    simp only [Pi.mul_apply]; rw [map_mul, ha m n h, hb m n h]
  one_mem' := by intro m n h; simp only [Pi.one_apply, map_one]
  add_mem' := by
    intro a b ha hb m n h
    simp only [Pi.add_apply]; rw [map_add, ha m n h, hb m n h]
  zero_mem' := by intro m n h; simp only [Pi.zero_apply, map_zero]
  neg_mem' := by
    intro a ha m n h
    simp only [Pi.neg_apply]; rw [map_neg, ha m n h]

def padicIntToInvLimRingHom : ℤ_[p] →+* padicInvLimSubring (p := p) where
  toFun z := ⟨fun n => PadicInt.toZModPow n z, by
    intro m n h
    exact congr_fun (congrArg DFunLike.coe
      (PadicInt.zmod_cast_comp_toZModPow m n h)) z⟩
  map_zero' := by apply Subtype.ext; funext n; simp [map_zero]
  map_one' := by apply Subtype.ext; funext n; simp [map_one]
  map_add' := by intro x y; apply Subtype.ext; funext n; simp [map_add]
  map_mul' := by intro x y; apply Subtype.ext; funext n; simp [map_mul]

noncomputable def padicDigit (a : ℤ_[p]) (n : ℕ) : ℕ :=
  (a.appr (n + 1) - a.appr n) / p ^ n

def digitPartialSum (p : ℕ) (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => digitPartialSum p b n + p ^ n * b n

end AdicCompletionTopology
end
