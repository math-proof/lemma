/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part5


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSObservable (T L : ℕ) (hT : 0 < T) (z : ℂ) : ℂ :=
  endpointParafObservable (hexCSFiniteRegion T L hT).inRegion
    (hexCSFiniteRegion T L hT).start 1 z (5 / 8) hexChi

def HexCSLocalRelation (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ v : HexCSVertex T L,
    ∑ j : Fin 3,
      (hexAWMid v.1 j - hexAWPos v.1) *
        hexCSObservable T L hT (hexAWMid v.1 j) = 0

noncomputable def hexCSDomain (T L : ℕ) (hT : 0 < T)
    (hlocal : HexCSLocalRelation T L hT) :
    HexDomain (HexCSVertex T L) where
  interiorVertices := Finset.univ
  pos v := hexAWPos v.1
  mid v j := hexAWMid v.1 j
  obs := hexCSObservable T L hT
  relation := by
    intro v _
    exact hlocal v

def hexCSDomainInteriorPairing (T L : ℕ) (hT : 0 < T)
    (hlocal : HexCSLocalRelation T L hT) :
    (hexCSDomain T L hT hlocal).InteriorPairing where
  interior := hexCSInteriorIncidences T L
  pair := hexCSPairIncidence
  pair_mem := by
    intro e he
    rw [hexCS_mem_interior_iff] at he ⊢
    rw [hexCSPairIncidence_eq_mate e he]
    exact (hexCSInteriorMate ⟨e, he⟩).2
  pair_invol := by
    intro e he
    rw [hexCS_mem_interior_iff] at he
    have hm := (hexCSInteriorMate ⟨e, he⟩).2
    rw [hexCSPairIncidence_eq_mate e he,
      hexCSPairIncidence_eq_mate _ hm]
    exact congrArg Subtype.val (hexCSInteriorMate_invol ⟨e, he⟩)
  pair_ne := by
    intro e he
    rw [hexCS_mem_interior_iff] at he
    rw [hexCSPairIncidence_eq_mate e he]
    exact fun h => hexCSInteriorMate_ne ⟨e, he⟩ (Subtype.ext h)
  cancel := by
    intro e he
    rw [hexCS_mem_interior_iff] at he
    rw [hexCSPairIncidence_eq_mate e he]
    unfold HexDomain.incTerm
    change (hexAWMid e.vtx.1 e.edge - hexAWPos e.vtx.1) *
          hexCSObservable T L hT (hexAWMid e.vtx.1 e.edge) =
      -((hexAWMid (hexCSInteriorMate ⟨e, he⟩).1.vtx.1
            (hexCSInteriorMate ⟨e, he⟩).1.edge -
          hexAWPos (hexCSInteriorMate ⟨e, he⟩).1.vtx.1) *
            hexCSObservable T L hT
              (hexAWMid (hexCSInteriorMate ⟨e, he⟩).1.vtx.1
                (hexCSInteriorMate ⟨e, he⟩).1.edge))
    rw [hexCSInteriorMate_opposite, hexCSInteriorMate_mid]
    ring

end
end StatMech.Universality
