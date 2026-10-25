/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part6
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


set_option maxHeartbeats 1000000 in
@[simp] theorem mem_canonicalCoverageExclusiveBadQuadrangles_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p) :
    c ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p a b ↔
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ∧
        ¬ RowsDisconnect ends m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) k zero := by
  classical
  simp only [canonicalCoverageExclusiveBadQuadrangles,
    canonicalCoverageExclusive, Finset.mem_filter, Finset.mem_sdiff]
  tauto


theorem card_good_add_bad_eq_card_coverage_sdiff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    #(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b) +
      #(canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p a b) =
      #(canonicalCoverageExclusive ends m j k l zero p a b) := by
  classical
  exact Finset.card_filter_add_card_filter_not
    (fun c : leftMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) k zero)


theorem coverage_card_add_bad_swap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    #(canonicalMaskOrbitCoverage ends m j k l zero p a) +
        #(canonicalCoverageExclusiveBadQuadrangles
          ends m j k l zero p b a) =
      #(canonicalMaskOrbitCoverage ends m j k l zero p b) +
        #(canonicalCoverageExclusiveBadQuadrangles
          ends m j k l zero p a b) := by
  classical
  let A := canonicalMaskOrbitCoverage ends m j k l zero p a
  let B := canonicalMaskOrbitCoverage ends m j k l zero p b
  let GAB := canonicalCoverageExclusiveGoodQuadrangles
    ends m j k l zero p a b
  let GBA := canonicalCoverageExclusiveGoodQuadrangles
    ends m j k l zero p b a
  let DAB := canonicalCoverageExclusiveBadQuadrangles
    ends m j k l zero p a b
  let DBA := canonicalCoverageExclusiveBadQuadrangles
    ends m j k l zero p b a
  have hgood : #GAB = #GBA :=
    card_canonicalCoverageExclusiveGoodQuadrangles_comm
      ends m j k l zero hloop hjk hkl p a b hab
  have hAB : #GAB + #DAB = #(A \ B) := by
    simpa only [canonicalCoverageExclusive] using
      card_good_add_bad_eq_card_coverage_sdiff
        ends m j k l zero p a b
  have hBA : #GBA + #DBA = #(B \ A) := by
    simpa only [canonicalCoverageExclusive] using
      card_good_add_bad_eq_card_coverage_sdiff
        ends m j k l zero p b a
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  have hinter : #(A ∩ B) = #(B ∩ A) := by rw [Finset.inter_comm]
  change #A + #DBA = #B + #DAB
  omega


theorem coverage_card_lt_of_mem_bad_of_opposite_bad_eq_empty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b)
    (hopposite : canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p b a = ∅) :
    #(canonicalMaskOrbitCoverage ends m j k l zero p b) <
      #(canonicalMaskOrbitCoverage ends m j k l zero p a) := by
  have hbalance := coverage_card_add_bad_swap
    ends m j k l zero hloop hjk hkl p a b hab
  have hbadPos : 0 < #(canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :=
    Finset.card_pos.mpr ⟨c, hc⟩
  rw [hopposite, Finset.card_empty, Nat.add_zero] at hbalance
  omega

end StatMech.GrahamGHS.FourColor
