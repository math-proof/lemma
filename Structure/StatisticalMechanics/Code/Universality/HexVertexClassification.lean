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
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


structure HexSawClassification (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  
  pairs : Finset ℕ
  
  pairBase : ℕ → List ℤ
  
  pairLq : ℕ → List ℤ
  
  pairLr : ℕ → List ℤ
  
  pairLq_sum : ∀ P ∈ pairs, (pairLq P).sum = -4
  
  pairLr_sum : ∀ P ∈ pairs, (pairLr P).sum = 4
  
  pairLen : ∀ P ∈ pairs, (pairLq P).length = (pairLr P).length
  
  pairQ_valid : ∀ P ∈ pairs,
    (ofTurns a h0 (pairBase P ++ pairLq P)).IsLegalSAW
      ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).StaysIn region
      ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).EndsAt (v + hexOmega * du)
  
  pairR_valid : ∀ P ∈ pairs,
    (ofTurns a h0 (pairBase P ++ pairLr P)).IsLegalSAW
      ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).StaysIn region
      ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).EndsAt (v + hexOmega ^ 2 * du)
  


  pairQ_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLq P) (v + du)
  

  pairQ_passes_r : ∀ P ∈ pairs,
    PassesThrough a h0 (pairBase P ++ pairLq P) (v + hexOmega ^ 2 * du)
  

  pairR_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLr P) (v + du)
  

  pairR_passes_q : ∀ P ∈ pairs,
    PassesThrough a h0 (pairBase P ++ pairLr P) (v + hexOmega * du)
  
  triplets : Finset ℕ
  
  tripBase : ℕ → List ℤ
  
  tripP_valid : ∀ T ∈ triplets,
    (ofTurns a h0 (tripBase T)).IsLegalSAW
      ∧ (ofTurns a h0 (tripBase T)).StaysIn region
      ∧ (ofTurns a h0 (tripBase T)).EndsAt (v + du)
  
  tripQ_valid : ∀ T ∈ triplets,
    (ofTurns a h0 (tripBase T ++ [-1])).IsLegalSAW
      ∧ (ofTurns a h0 (tripBase T ++ [-1])).StaysIn region
      ∧ (ofTurns a h0 (tripBase T ++ [-1])).EndsAt (v + hexOmega * du)
  
  tripR_valid : ∀ T ∈ triplets,
    (ofTurns a h0 (tripBase T ++ [1])).IsLegalSAW
      ∧ (ofTurns a h0 (tripBase T ++ [1])).StaysIn region
      ∧ (ofTurns a h0 (tripBase T ++ [1])).EndsAt (v + hexOmega ^ 2 * du)
  


  tripQ_not_passes_r : ∀ T ∈ triplets,
    ¬ PassesThrough a h0 (tripBase T ++ [-1]) (v + hexOmega ^ 2 * du)
  

  tripR_not_passes_q : ∀ T ∈ triplets,
    ¬ PassesThrough a h0 (tripBase T ++ [1]) (v + hexOmega * du)
  
  tripBase_inj : ∀ T1 T2 : triplets, tripBase T1 = tripBase T2 → T1 = T2
  
  pairQ_inj : ∀ P1 P2 : pairs,
    pairBase P1 ++ pairLq P1 = pairBase P2 ++ pairLq P2 → P1 = P2
  
  pairR_inj : ∀ P1 P2 : pairs,
    pairBase P1 ++ pairLr P1 = pairBase P2 ++ pairLr P2 → P1 = P2
  


  classify_p : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + du) →
    ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts
  


  classify_q : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
    (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts)
      ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts)
  


  classify_r : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
    (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts)
      ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts)
  


  reindex :
    (((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
    = (∑ P ∈ pairs,
        (((v + hexOmega * du) - v)
            * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (pairBase P ++ pairLq P)
          + ((v + hexOmega ^ 2 * du) - v)
              * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (pairBase P ++ pairLr P)))
      + (∑ T ∈ triplets,
          (((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi (tripBase T)
            + ((v + hexOmega * du) - v)
                * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (tripBase T ++ [-1])
            + ((v + hexOmega ^ 2 * du) - v)
                * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tripBase T ++ [1])))

end StatMech.Universality
