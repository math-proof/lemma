/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexEnum.Part3


namespace StatMech.Universality

open Complex

open HexWalk


structure HexVertexEnumeration (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) where
  
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
