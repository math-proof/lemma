/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part4
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


@[simp] theorem uniformMaskCanonicalSelector_balancedSwap
    (ends : ι -> Sym2 W) (m X Y : Finset ι) (j k l zero : W)
    (c : ↑m -> Fin 4) :
    uniformMaskCanonicalSelector ends m j k l zero
        (balancedSwap m X Y c) =
      uniformMaskCanonicalSelector ends m j k l zero c := by
  simp [uniformMaskCanonicalSelector]


theorem uniformMaskCanonicalSelector_valid_sources
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    let s := uniformMaskCanonicalSelector ends m j k l zero c
    s.1 ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧
      s.2 ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧
      sources ends s.1 = {k, l} ∧
      sources ends s.2 = ∅ := by
  let p := fourColorMaskProfile m c
  let r := leftMaskReference ends m j k l zero p
  have hex : ∃ d : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero d ∧
        fourColorMaskProfile m d = p := ⟨c, hc, rfl⟩
  have hr := leftMaskReference_spec ends m j k l zero p hex
  have hv := canonicalTransfers_valid hloop hjk hkl hr.1
  have hprofile : fourColorMaskProfile m r = fourColorMaskProfile m c := by
    exact hr.2
  have hmid : middleMask m r = middleMask m c :=
    congrArg Prod.fst hprofile
  have hout : outerMask m r = outerMask m c :=
    congrArg Prod.snd hprofile
  have hX : canonicalMiddleTransfer ends m r k zero ⊆
      colorClass m c 1 ∪ colorClass m c 2 := by
    have : canonicalMiddleTransfer ends m r k zero ⊆ middleMask m r := by
      simpa only [middleMask] using hv.1
    rw [hmid] at this
    simpa only [middleMask] using this
  have hY : canonicalOuterTransfer ends m r k zero ⊆
      colorClass m c 0 ∪ colorClass m c 3 := by
    have : canonicalOuterTransfer ends m r k zero ⊆ outerMask m r := by
      simpa only [outerMask] using hv.2.1
    rw [hout] at this
    simpa only [outerMask] using this
  change
    (uniformMaskCanonicalSelector ends m j k l zero c).1 ⊆
        colorClass m c 1 ∪ colorClass m c 2 ∧
      (uniformMaskCanonicalSelector ends m j k l zero c).2 ⊆
        colorClass m c 0 ∪ colorClass m c 3 ∧
      sources ends
          (uniformMaskCanonicalSelector ends m j k l zero c).1 = {k, l} ∧
      sources ends
          (uniformMaskCanonicalSelector ends m j k l zero c).2 = ∅
  simpa only [uniformMaskCanonicalSelector, p, r] using
    And.intro hX (And.intro hY (And.intro hv.2.2.1 hv.2.2.2))


theorem GrahamFiberMinor_of_uniformMaskCanonicalTransfer
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hdisconnect : ∀ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ->
        let s := uniformMaskCanonicalSelector ends m j k l zero c
        RowsDisconnect ends m (balancedSwap m s.1 s.2 c) k zero) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_balancedSelector ends m j k l zero
    (uniformMaskCanonicalSelector ends m j k l zero)
  · intro c hc
    have hv := uniformMaskCanonicalSelector_valid_sources
      hloop hjk hkl hc
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hdisconnect c hc⟩
  · intro c
    exact uniformMaskCanonicalSelector_balancedSwap
      ends m _ _ j k l zero c


theorem GrahamFiberMinor_of_canonicalTransferDescent
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hdescent : ∀ c d : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ->
      LeftPattern ends m {j, k} {k, l} k zero d ->
      fourColorMaskProfile m c = fourColorMaskProfile m d ->
      ¬ RowsDisconnect ends m
          (balancedSwap m
            (canonicalMiddleTransfer ends m c k zero)
            (canonicalOuterTransfer ends m c k zero) d) k zero ->
      canonicalTransferSize ends m k zero d <
        canonicalTransferSize ends m k zero c) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_uniformMaskCanonicalTransfer
    ends m j k l zero hloop hjk hkl
  intro d hd
  let p := fourColorMaskProfile m d
  let r := leftMaskReference ends m j k l zero p
  have hex : ∃ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ∧
        fourColorMaskProfile m c = p := ⟨d, hd, rfl⟩
  have hr := leftMaskReference_spec ends m j k l zero p hex
  have hmin := leftMaskReference_minimal ends m j k l zero p
    hex d hd rfl
  change RowsDisconnect ends m
    (balancedSwap m
      (canonicalMiddleTransfer ends m r k zero)
      (canonicalOuterTransfer ends m r k zero) d) k zero
  by_contra hbad
  have hlt := hdescent r d hr.1 hd (by simpa [p] using hr.2) hbad
  exact (not_lt_of_ge hmin) hlt


theorem GrahamFiberMinor_of_canonicalTransferStrictSubset
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hproper : ∀ c d : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ->
      LeftPattern ends m {j, k} {k, l} k zero d ->
      fourColorMaskProfile m c = fourColorMaskProfile m d ->
      ¬ RowsDisconnect ends m
          (balancedSwap m
            (canonicalMiddleTransfer ends m c k zero)
            (canonicalOuterTransfer ends m c k zero) d) k zero ->
      canonicalTransferUnion ends m k zero d ⊂
        canonicalTransferUnion ends m k zero c) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalTransferDescent
    ends m j k l zero hloop hjk hkl
  intro c d hc hd hprofile hbad
  rw [canonicalTransferSize_eq_card_union hloop hjk hkl hc,
    canonicalTransferSize_eq_card_union hloop hjk hkl hd]
  exact Finset.card_lt_card (hproper c d hc hd hprofile hbad)

end StatMech.GrahamGHS.FourColor
