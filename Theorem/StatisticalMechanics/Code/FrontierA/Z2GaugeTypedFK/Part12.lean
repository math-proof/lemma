/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedReachabilitySpin_compatible
    (ends : P -> V × V) (omega : P -> Bool) (x : V) :
    TypedSignedCompatible ends ∅ omega
      (typedReachabilitySpin ends omega x) := by
  intro p hp
  have hagree : typedReachabilitySpin ends omega x (ends p).1 =
      typedReachabilitySpin ends omega x (ends p).2 := by
    by_cases heq : (ends p).1 = (ends p).2
    · rw [heq]
    · have hadj : (typedOpenGraph ends omega).Adj
          (ends p).1 (ends p).2 :=
        ⟨p, hp, Or.inl ⟨rfl, rfl⟩, heq⟩
      have huv := hadj.reachable
      by_cases hu : (typedOpenGraph ends omega).Reachable x (ends p).1
      · have hv := hu.trans huv
        simp [typedReachabilitySpin, hu, hv]
      · have hv : ¬ (typedOpenGraph ends omega).Reachable x (ends p).2 :=
          fun hv => hu (hv.trans huv.symm)
        simp [typedReachabilitySpin, hu, hv]
  simpa using hagree

theorem typedSignedCompatible_empty_xor_iff
    (ends : P -> V × V) (omega : P -> Bool)
    (sigma tau : V -> Bool)
    (htau : TypedSignedCompatible ends ∅ omega tau) :
    TypedSignedCompatible ends ∅ omega (typedSpinXor sigma tau) <->
      TypedSignedCompatible ends ∅ omega sigma := by
  have preserve : forall s : V -> Bool,
      TypedSignedCompatible ends ∅ omega s ->
      TypedSignedCompatible ends ∅ omega (typedSpinXor s tau) := by
    intro s hs p hp
    have hse : s (ends p).1 = s (ends p).2 := (hs p hp).2 (by simp)
    have hte : tau (ends p).1 = tau (ends p).2 :=
      (htau p hp).2 (by simp)
    simp [typedSpinXor, hse, hte]
  constructor
  · intro hs
    have h := preserve (typedSpinXor sigma tau) hs
    rwa [typedSpinXor_cancel_right] at h
  · exact preserve sigma


theorem typedSignedCompatible_xor_iff_symmDiff_cut
    (ends : P -> V × V) (D : Finset P) (omega : P -> Bool)
    (sigma tau : V -> Bool) :
    TypedSignedCompatible ends D omega (typedSpinXor sigma tau) <->
      TypedSignedCompatible ends (D ∆ multibondCut ends tau) omega sigma := by
  constructor <;> intro h p hp
  · have hh := h p hp
    change (((sigma (ends p).1).xor (tau (ends p).1) =
      (sigma (ends p).2).xor (tau (ends p).2)) <-> p ∉ D) at hh
    rw [bool_xor_eq_xor_iff_eq_iff_eq] at hh
    simp only [Finset.mem_symmDiff, mem_multibondCut]
    tauto
  · have hh := h p hp
    simp only [Finset.mem_symmDiff, mem_multibondCut] at hh
    change (((sigma (ends p).1).xor (tau (ends p).1) =
      (sigma (ends p).2).xor (tau (ends p).2)) <-> p ∉ D)
    rw [bool_xor_eq_xor_iff_eq_iff_eq]
    tauto

theorem typedSpinProduct_xor_reachability_of_not_reachable
    (ends : P -> V × V) (omega : P -> Bool) (sigma : V -> Bool)
    {x y : V} (hxy : ¬ (typedOpenGraph ends omega).Reachable x y) :
    typedSpinProduct
        (typedSpinXor sigma (typedReachabilitySpin ends omega x)) x y =
      -typedSpinProduct sigma x y := by
  cases hx : sigma x <;> cases hy : sigma y <;>
    simp [typedSpinProduct, typedSpinXor, typedReachabilitySpin, hxy, hx, hy]


theorem typedCompatibleSpinProduct_sum_eq_zero_of_not_reachable
    (ends : P -> V × V) (omega : P -> Bool) {x y : V}
    (hxy : ¬ (typedOpenGraph ends omega).Reachable x y) :
    (∑ sigma : V -> Bool,
      (if TypedSignedCompatible ends ∅ omega sigma then (1 : Real) else 0) *
        typedSpinProduct sigma x y) = 0 := by
  let tau := typedReachabilitySpin ends omega x
  let F : (V -> Bool) -> Real := fun sigma =>
    (if TypedSignedCompatible ends ∅ omega sigma then (1 : Real) else 0) *
      typedSpinProduct sigma x y
  have htau : TypedSignedCompatible ends ∅ omega tau :=
    typedReachabilitySpin_compatible ends omega x
  have hmap : forall sigma : V -> Bool,
      F (typedSpinXor sigma tau) = -F sigma := by
    intro sigma
    have hcompat := typedSignedCompatible_empty_xor_iff
      ends omega sigma tau htau
    have hspin := typedSpinProduct_xor_reachability_of_not_reachable
      ends omega sigma hxy
    simp only [F]
    rw [if_congr hcompat rfl rfl, hspin]
    ring
  have hreindex := (typedSpinXorEquiv tau).sum_comp F
  have hneg : (∑ sigma : V -> Bool, F sigma) =
      -(∑ sigma : V -> Bool, F sigma) := by
    calc
      (∑ sigma : V -> Bool, F sigma) =
          ∑ sigma : V -> Bool, F (typedSpinXor sigma tau) := hreindex.symm
      _ = ∑ sigma : V -> Bool, -F sigma := by
        apply Finset.sum_congr rfl
        intro sigma _
        exact hmap sigma
      _ = -(∑ sigma : V -> Bool, F sigma) := by simp
  change (∑ sigma : V -> Bool, F sigma) = 0
  linarith


theorem typedESWeight_spinProduct_sum_eq
    (ends : P -> V × V) (rho : P -> Real) (omega : P -> Bool)
    (x y : V) :
    (∑ sigma : V -> Bool,
      typedESWeight ends rho ∅ sigma omega * typedSpinProduct sigma x y) =
      if (typedOpenGraph ends omega).Reachable x y then
        typedFKWeight ends rho omega else 0 := by
  by_cases hxy : (typedOpenGraph ends omega).Reachable x y
  · rw [if_pos hxy]
    unfold typedFKWeight
    apply Finset.sum_congr rfl
    intro sigma _
    by_cases hsigma : TypedSignedCompatible ends ∅ omega sigma
    · have heq := typedSignedCompatible_empty_eq_of_reachable
        ends omega sigma hsigma hxy
      rw [typedSpinProduct]
      simp [heq]
    · rw [typedESWeight_factor]
      simp [hsigma]
  · rw [if_neg hxy]
    simp_rw [typedESWeight_factor]
    have hzero := typedCompatibleSpinProduct_sum_eq_zero_of_not_reachable
      ends omega hxy
    calc
      (∑ sigma : V -> Bool,
          (typedESActivity rho omega *
              if TypedSignedCompatible ends ∅ omega sigma then 1 else 0) *
            typedSpinProduct sigma x y) =
          typedESActivity rho omega *
            ∑ sigma : V -> Bool,
              (if TypedSignedCompatible ends ∅ omega sigma then 1 else 0) *
                typedSpinProduct sigma x y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma _
        ring
      _ = 0 := by rw [hzero, mul_zero]


end
end StatMech.FrontierA
