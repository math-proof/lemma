/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

theorem cubicalVolumeBoundary_isClosed {a b c : Nat}
    (S : Finset (CubicalCell a b c)) :
    IsClosedPlaquetteSet cubicalPlaquetteIncidence
      (cubicalVolumeBoundary S) := by
  induction S using Finset.induction_on with
  | empty =>
      intro e
      simp [cubicalVolumeBoundary, gaugeSurfaceBoundary]
  | @insert q S hq ih =>
      rw [cubicalVolumeBoundary, gaugeSurfaceBoundary_insert _ _ _ hq]
      intro e
      apply (even_plaquetteIncidenceCount_symmDiff_iff
        cubicalPlaquetteIncidence (cubicalCellFaces q)
        (cubicalVolumeBoundary S) e).mpr
      exact ⟨fun _ => ih e, fun _ => cubicalCellFaces_isClosed q e⟩


theorem not_mem_of_even_unique_incident
    {E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P)
    (p : P) (e : E) (hpe : e ∈ incidence p)
    (heven : Even (plaquetteIncidenceCount incidence A e))
    (hunique : ∀ q ∈ A, e ∈ incidence q → q = p) :
    p ∉ A := by
  intro hp
  have hfilter : A.filter (fun q => e ∈ incidence q) = {p} := by
    ext q
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hqA, hqe⟩
      exact hunique q hqA hqe
    · intro hqp
      subst q
      exact ⟨hp, hpe⟩
  rw [plaquetteIncidenceCount_eq_filter_card, hfilter] at heven
  norm_num at heven

set_option linter.flexible false in


theorem volume_eq_empty_of_lowerXY_boundary_not_mem
    {a b c : Nat} (hc : 0 < c) (S : Finset (CubicalCell a b c))
    (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ cubicalVolumeBoundary S) :
    S = ∅ := by
  cases c with
  | zero => omega
  | succ c =>
      have hcell : ∀ (i : Fin a) (j : Fin b) (k : Fin (c + 1)),
          CubicalCell.mk i j k ∉ S := by
        intro i j k
        induction k using Fin.induction with
        | zero =>
            apply not_mem_of_even_unique_incident cubicalCellFaces S
              ⟨i, j, 0⟩ (.xy i j 0) (by simp [cubicalCellFaces])
            · have hnot := hxy i j 0
              simpa [cubicalVolumeBoundary] using hnot
            · intro q hqS hqface
              rcases q with ⟨i', j', k'⟩
              simp [cubicalCellFaces] at hqface
              rcases hqface with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
              · have hk' : k' = 0 := by
                  have hkcast : (0 : Fin (c + 1)).castSucc = k'.castSucc := by
                    simpa using hk
                  exact (Fin.castSucc_injective _ hkcast).symm
                subst k'
                rfl
              · have hv := congrArg Fin.val hk
                simp at hv
        | succ k ih =>
            apply not_mem_of_even_unique_incident cubicalCellFaces S
              ⟨i, j, k.succ⟩ (.xy i j k.succ.castSucc)
              (by simp [cubicalCellFaces])
            · have hnot := hxy i j k.succ
              simpa [cubicalVolumeBoundary] using hnot
            · intro q hqS hqface
              rcases q with ⟨i', j', z'⟩
              simp [cubicalCellFaces] at hqface
              rcases hqface with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩
              · have hztarget : z' = k.succ := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hz
                  simp at hv ⊢
                  omega
                subst z'
                rfl
              · have hzprev : z' = k.castSucc := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hz
                  simp at hv ⊢
                  omega
                subst z'
                exact False.elim (ih hqS)
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨q, hq⟩
      rcases q with ⟨i, j, k⟩
      exact hcell i j k hq

set_option linter.flexible false in


theorem closed_xz_not_mem_of_lowerXY_not_mem
    {a b c : Nat} (hc : 0 < c)
    (A : Finset (CubicalPlaquette a b c))
    (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
    (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ A) :
    ∀ (i : Fin a) (j : Fin (b + 1)) (k : Fin c),
      CubicalPlaquette.xz i j k ∉ A := by
  cases c with
  | zero => omega
  | succ c =>
      intro i j k
      induction k using Fin.induction with
      | zero =>
          apply closed_not_mem_of_unique_incident cubicalPlaquetteIncidence
            A hclosed (.xz i j 0) (.x i j 0) (by
              simp [cubicalPlaquetteIncidence])
          intro q hqA hqe
          cases q with
          | xy i' j' k' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
              · have hk' : k' = 0 := by
                  apply Fin.ext
                  simpa using (congrArg Fin.val hk).symm
                subst k'
                exact False.elim (hxy i j' 0 hqA)
              · have hk' : k' = 0 := by
                  apply Fin.ext
                  simpa using (congrArg Fin.val hk).symm
                subst k'
                exact False.elim (hxy i j' 0 hqA)
          | xz i' j' k' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
              · have hk' : k' = 0 := by
                  have hkcast : (0 : Fin (c + 1)).castSucc = k'.castSucc := by
                    simpa using hk
                  exact (Fin.castSucc_injective _ hkcast).symm
                subst k'
                rfl
              · have hv := congrArg Fin.val hk
                simp at hv
          | yz i' j' k' =>
              simp [cubicalPlaquetteIncidence] at hqe
      | succ k ih =>
          apply closed_not_mem_of_unique_incident cubicalPlaquetteIncidence
            A hclosed (.xz i j k.succ) (.x i j k.succ.castSucc) (by
              simp [cubicalPlaquetteIncidence])
          intro q hqA hqe
          cases q with
          | xy i' j' z' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩
              · rw [← hz] at hqA
                exact False.elim (hxy i j' k.succ hqA)
              · rw [← hz] at hqA
                exact False.elim (hxy i j' k.succ hqA)
          | xz i' j' z' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩
              · have hztarget : z' = k.succ := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hz
                  simp at hv ⊢
                  omega
                subst z'
                rfl
              · have hzpred : z' = k.castSucc := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hz
                  simp at hv ⊢
                  omega
                subst z'
                exact False.elim (ih hqA)
          | yz i' j' z' =>
              simp [cubicalPlaquetteIncidence] at hqe

set_option linter.flexible false in


theorem closed_yz_not_mem_of_lowerXY_not_mem
    {a b c : Nat} (hc : 0 < c)
    (A : Finset (CubicalPlaquette a b c))
    (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
    (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ A) :
    ∀ (i : Fin (a + 1)) (j : Fin b) (k : Fin c),
      CubicalPlaquette.yz i j k ∉ A := by
  cases c with
  | zero => omega
  | succ c =>
      intro i j k
      induction k using Fin.induction with
      | zero =>
          apply closed_not_mem_of_unique_incident cubicalPlaquetteIncidence
            A hclosed (.yz i j 0) (.y i j 0) (by
              simp [cubicalPlaquetteIncidence])
          intro q hqA hqe
          cases q with
          | xy i' j' k' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
              · have hk' : k' = 0 := by
                  apply Fin.ext
                  simpa using (congrArg Fin.val hk).symm
                subst k'
                exact False.elim (hxy i' j 0 hqA)
              · have hk' : k' = 0 := by
                  apply Fin.ext
                  simpa using (congrArg Fin.val hk).symm
                subst k'
                exact False.elim (hxy i' j 0 hqA)
          | xz i' j' k' =>
              simp [cubicalPlaquetteIncidence] at hqe
          | yz i' j' k' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
              · have hk' : k' = 0 := by
                  have hkcast : (0 : Fin (c + 1)).castSucc = k'.castSucc := by
                    simpa using hk
                  exact (Fin.castSucc_injective _ hkcast).symm
                subst k'
                rfl
              · have hv := congrArg Fin.val hk
                simp at hv
      | succ k ih =>
          apply closed_not_mem_of_unique_incident cubicalPlaquetteIncidence
            A hclosed (.yz i j k.succ) (.y i j k.succ.castSucc) (by
              simp [cubicalPlaquetteIncidence])
          intro q hqA hqe
          cases q with
          | xy x' j' z' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩
              · rw [← hz] at hqA
                exact False.elim (hxy x' j k.succ hqA)
              · rw [← hz] at hqA
                exact False.elim (hxy x' j k.succ hqA)
          | xz x' j' z' =>
              simp [cubicalPlaquetteIncidence] at hqe
          | yz x' j' z' =>
              simp [cubicalPlaquetteIncidence] at hqe
              rcases hqe with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩
              · have hztarget : z' = k.succ := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hz
                  simp at hv ⊢
                  omega
                subst z'
                rfl
              · have hzpred : z' = k.castSucc := by
                  apply Fin.ext
                  have hv := congrArg Fin.val hz
                  simp at hv ⊢
                  omega
                subst z'
                exact False.elim (ih hqA)

set_option linter.flexible false in


theorem closed_topXY_not_mem_of_lowerXY_not_mem
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c)
    (A : Finset (CubicalPlaquette a b c))
    (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
    (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ A)
    (hxz : ∀ (i : Fin a) (j : Fin (b + 1)) (k : Fin c),
      CubicalPlaquette.xz i j k ∉ A) :
    ∀ (i : Fin a) (j : Fin b),
      CubicalPlaquette.xy i j (Fin.last c) ∉ A := by
  cases b with
  | zero => omega
  | succ b =>
      cases c with
      | zero => omega
      | succ c =>
          intro i j
          induction j using Fin.induction with
          | zero =>
              apply closed_not_mem_of_unique_incident cubicalPlaquetteIncidence
                A hclosed (.xy i 0 (Fin.last (c + 1)))
                (.x i 0 (Fin.last (c + 1))) (by
                  simp [cubicalPlaquetteIncidence])
              intro q hqA hqe
              cases q with
              | xy i' j' z' =>
                  simp [cubicalPlaquetteIncidence] at hqe
                  rcases hqe with ⟨rfl, hj, rfl⟩ | ⟨rfl, hj, rfl⟩
                  · have hj' : j' = 0 := by
                      have hjcast : (0 : Fin (b + 1)).castSucc = j'.castSucc := by
                        simpa using hj
                      exact (Fin.castSucc_injective _ hjcast).symm
                    subst j'
                    rfl
                  · have hv := congrArg Fin.val hj
                    simp at hv
              | xz i' j' z' =>
                  simp [cubicalPlaquetteIncidence] at hqe
                  rcases hqe with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩
                  · have hv := congrArg Fin.val hz
                    simp at hv
                    omega
                  · exact False.elim (hxz _ _ _ hqA)
              | yz i' j' z' =>
                  simp [cubicalPlaquetteIncidence] at hqe
          | succ j ih =>
              apply closed_not_mem_of_unique_incident cubicalPlaquetteIncidence
                A hclosed (.xy i j.succ (Fin.last (c + 1)))
                (.x i j.succ.castSucc (Fin.last (c + 1))) (by
                  simp [cubicalPlaquetteIncidence])
              intro q hqA hqe
              cases q with
              | xy i' j' z' =>
                  simp [cubicalPlaquetteIncidence] at hqe
                  rcases hqe with ⟨rfl, hj, rfl⟩ | ⟨rfl, hj, rfl⟩
                  · have hjtarget : j' = j.succ := by
                      apply Fin.ext
                      have hv := congrArg Fin.val hj
                      simp at hv ⊢
                      omega
                    subst j'
                    rfl
                  · have hjprev : j' = j.castSucc := by
                      apply Fin.ext
                      have hv := congrArg Fin.val hj
                      simp at hv ⊢
                      omega
                    subst j'
                    exact False.elim (ih hqA)
              | xz i' j' z' =>
                  simp [cubicalPlaquetteIncidence] at hqe
                  rcases hqe with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩
                  · have hv := congrArg Fin.val hz
                    simp at hv
                    omega
                  · exact False.elim (hxz _ _ _ hqA)
              | yz i' j' z' =>
                  simp [cubicalPlaquetteIncidence] at hqe


theorem closed_eq_empty_of_lowerXY_not_mem
    {a b c : Nat} (hb : 0 < b) (hc : 0 < c)
    (A : Finset (CubicalPlaquette a b c))
    (hclosed : IsClosedPlaquetteSet cubicalPlaquetteIncidence A)
    (hxy : ∀ (i : Fin a) (j : Fin b) (k : Fin c),
      CubicalPlaquette.xy i j k.castSucc ∉ A) :
    A = ∅ := by
  have hxz := closed_xz_not_mem_of_lowerXY_not_mem hc A hclosed hxy
  have hyz := closed_yz_not_mem_of_lowerXY_not_mem hc A hclosed hxy
  have htop := closed_topXY_not_mem_of_lowerXY_not_mem hb hc A hclosed hxy hxz
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨p, hp⟩
  cases p with
  | xy i j k =>
      revert hp
      refine Fin.lastCases ?_ ?_ k
      · exact htop i j
      · intro z
        exact hxy i j z
  | xz i j k => exact hxz i j k hp
  | yz i j k => exact hyz i j k hp

end
end StatMech.FrontierA
