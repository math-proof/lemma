/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Def.StatisticalMechanics.Code.Universality.HexPairingMaps.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexPairing_vertex_relation_of_classification (R : HexFiniteRegion)
    (C : HexSawClassification R.inRegion a h0 v du) (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand R.inRegion a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  hexClass_vertex_relation C hdu hp hq hr


theorem hexPairing_emptySupport_summand_zero (a w : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (haz : a ≠ z) (ts : List ℤ) :
    parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts = 0 := by
  have hend0 : (ofTurns a h0 ([] : List ℤ)).endMid = a := trivialWalk_endMid a h0
  unfold parafSummand
  rw [if_neg]
  rintro ⟨hlegal, hstay, hend⟩
  have hnil : ts = [] := hexFiniteRegion_single_length a w h0 ts hclosure hlegal.2 hstay
  subst hnil
  rw [HexWalk.EndsAt, hend0] at hend
  exact haz hend


theorem hexPairing_emptySupport_summable (a w : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (haz : a ≠ z) :
    Summable fun ts => parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts := by
  rw [show (fun ts => parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts)
        = (fun _ => (0 : ℂ)) from
      funext fun ts => hexPairing_emptySupport_summand_zero a w h0 z σ x hclosure haz ts]
  exact summable_zero


theorem hexPairing_emptySupport_vertex_relation (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    ((v + du) - v)
        * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = 0 :=
  hexPairing_vertex_relation_of_classification
    (hexFiniteRegion_single a w hclosure)
    (hexPairing_emptySupport_classification a w h0 v du hdu hclosure hap haq har) hdu
    (hexPairing_emptySupport_summable a w h0 (v + du) (5/8) hexChi hclosure hap)
    (hexPairing_emptySupport_summable a w h0 (v + hexOmega * du) (5/8) hexChi hclosure haq)
    (hexPairing_emptySupport_summable a w h0 (v + hexOmega ^ 2 * du) (5/8) hexChi hclosure har)


theorem hexPairing_covering (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset
          (a := a) (h0 := h0) (v := v) (du := du) hdu,
        (ofTurns a h0 ts).EndsAt (v + du) →
        ∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T = ts)
      ∧ (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset
            (a := a) (h0 := h0) (v := v) (du := du) hdu,
          (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
          (∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T ++ [-1] = ts)
            ∨ (∃ P ∈ (∅ : Finset ℕ),
                (fun _ : ℕ => ([] : List ℤ)) P ++ (fun _ : ℕ => ([] : List ℤ)) P = ts))
      ∧ (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset
            (a := a) (h0 := h0) (v := v) (du := du) hdu,
          (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
          (∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T ++ [1] = ts)
            ∨ (∃ P ∈ (∅ : Finset ℕ),
                (fun _ : ℕ => ([] : List ℤ)) P ++ (fun _ : ℕ => ([] : List ℤ)) P = ts)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro ts hts _
    exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
      (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts)


end StatMech.Universality
