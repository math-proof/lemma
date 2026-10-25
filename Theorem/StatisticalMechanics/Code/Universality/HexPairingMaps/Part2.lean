/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Def.StatisticalMechanics.Code.Universality.HexPairingMaps


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexPairing_emptySupport_observable_zero (a w : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (haz : a ≠ z) :
    parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x = 0 := by
  have hend0 : (ofTurns a h0 ([] : List ℤ)).endMid = a := trivialWalk_endMid a h0
  unfold parafObservable
  have hfun : (fun ts => parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts)
      = (fun _ => (0 : ℂ)) := by
    funext ts
    unfold parafSummand
    rw [if_neg]
    rintro ⟨hlegal, hstay, hend⟩
    have hnil : ts = [] := hexFiniteRegion_single_length a w h0 ts hclosure hlegal.2 hstay
    subst hnil
    rw [HexWalk.EndsAt, hend0] at hend
    exact haz hend
  rw [hfun]; exact tsum_zero


theorem hexPairing_emptySupport (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du)
    (ts : List ℤ) :
    ts ∉ Function.support
      (combinedSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 v du) := by
  intro h
  obtain ⟨hlegal, hstay⟩ :=
    (hexFiniteRegion_single a w hclosure).support_isLegalSAW_staysIn hdu ts h
  have hnil : ts = [] :=
    hexFiniteRegion_single_length a w h0 ts hclosure hlegal.2 hstay
  subst hnil
  
  
  have hend : (ofTurns a h0 ([] : List ℤ)).endMid = a := trivialWalk_endMid a h0
  rcases support_endsAt_threeMid (region := (hexFiniteRegion_single a w hclosure).inRegion) [] h
    with hp | hq | hr
  · exact hap (by rw [HexWalk.EndsAt] at hp; rw [← hp, hend])
  · exact haq (by rw [HexWalk.EndsAt] at hq; rw [← hq, hend])
  · exact har (by rw [HexWalk.EndsAt] at hr; rw [← hr, hend])


end StatMech.Universality
