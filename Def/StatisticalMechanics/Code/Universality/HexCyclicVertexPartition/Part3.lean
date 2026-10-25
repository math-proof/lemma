/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part4


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


def HexCyclicLaunch.toTriplet
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn region)
    (hsuccMem : region (labelMid v du (hexCyclicSucc j)))
    (hpredMem : region (labelMid v du (hexCyclicPred j)))
    (hsuccFresh : hexCyclicNewVertex a h0 ts (-1) ∉
      (ofTurns a h0 ts).vertices)
    (hpredFresh : hexCyclicNewVertex a h0 ts 1 ∉
      (ofTurns a h0 ts).vertices) :
    HexCyclicTriplet region a h0 v du where
  baseLabel := j
  base := ts
  base_valid := ⟨hlegal, hstay, L.endsAt⟩
  succ_valid := by
    refine ⟨⟨hexCyclic_legalTurns_concat_single a h0 (-1) ts hlegal.1
      (Or.inr rfl), ?_⟩, ?_, L.succ_endsAt⟩
    · exact (hexCyclic_isSAW_concat_single_iff a h0 (-1) ts).2
        ⟨hlegal.2, hsuccFresh⟩
    · exact (hexCyclic_staysIn_concat_single_iff region a h0 (-1) ts).2
        ⟨hstay, by simpa [L.succ_newMid] using hsuccMem⟩
  pred_valid := by
    refine ⟨⟨hexCyclic_legalTurns_concat_single a h0 1 ts hlegal.1
      (Or.inl rfl), ?_⟩, ?_, L.pred_endsAt⟩
    · exact (hexCyclic_isSAW_concat_single_iff a h0 1 ts).2
        ⟨hlegal.2, hpredFresh⟩
    · exact (hexCyclic_staysIn_concat_single_iff region a h0 1 ts).2
        ⟨hstay, by simpa [L.pred_newMid] using hpredMem⟩


def hexVisitClassFinset (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (k : ℕ) : Finset (List ℤ) :=
  (R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu).filter
    (fun ts => specialMidCount a h0 v du ts = k)

end
end StatMech.Universality
