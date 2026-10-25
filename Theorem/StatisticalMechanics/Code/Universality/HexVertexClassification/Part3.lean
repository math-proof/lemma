/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexSeparation.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexVertexCoverage
import Def.StatisticalMechanics.Code.Universality.HexVertexClassification.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexClass_vertex_relation_singleTriplet (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (tb : List ℤ) (hdu : du ≠ 0)
    (hp0 : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq0 : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr0 : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (hp : (ofTurns a h0 tb).IsLegalSAW ∧ (ofTurns a h0 tb).StaysIn region
        ∧ (ofTurns a h0 tb).EndsAt (v + du))
    (hq : (ofTurns a h0 (tb ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [-1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (tb ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [1])).EndsAt (v + hexOmega ^ 2 * du))
    (hQr : ¬ PassesThrough a h0 (tb ++ [-1]) (v + hexOmega ^ 2 * du))
    (hRq : ¬ PassesThrough a h0 (tb ++ [1]) (v + hexOmega * du))
    (hcp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) → tb = ts)
    (hcq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → tb ++ [-1] = ts)
    (hcr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → tb ++ [1] = ts)
    (hreindex :
      (((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
        + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
        + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi tb
          + ((v + hexOmega * du) - v)
              * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (tb ++ [-1])
          + ((v + hexOmega ^ 2 * du) - v)
              * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tb ++ [1])) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  hexClass_vertex_relation
    (singleTriplet region a h0 v du tb hp hq hr hQr hRq hcp hcq hcr hreindex)
    hdu hp0 hq0 hr0

end StatMech.Universality
