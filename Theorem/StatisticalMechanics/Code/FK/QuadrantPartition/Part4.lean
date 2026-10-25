/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part6
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


namespace EdgeCount

theorem shift_adj (d n : ℕ) (i : Fin d) (x : Site d) (b : ℤ) (hb : b = 1 ∨ b = -1) :
    (hypercubicLattice d).Adj x (Function.update x i (x i + b)) := by
  classical
  rw [hypercubicLattice_adj, Finset.sum_eq_single i]
  · simp only [Function.update_self]; rcases hb with h|h <;> simp [h]
  · intro c _ hc; rw [Function.update_of_ne hc]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem card_shiftDom (d n : ℕ) (i : Fin d) (b : ℤ) (hb : b = 1 ∨ b = -1) (hd : 1 ≤ d) :
    (shiftDom d n i b).card = (2 * n) * (2 * n + 1) ^ (d - 1) := by
  unfold shiftDom boxSV_boxF
  have heq : ((Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)).filter
      (fun x => x i + b ∈ Finset.Icc (-(n : ℤ)) n))
      = Fintype.piFinset (fun j : Fin d =>
          if j = i then ((Finset.Icc (-(n : ℤ)) n).filter (fun v => v + b ∈ Finset.Icc (-(n:ℤ)) n))
                   else Finset.Icc (-(n : ℤ)) n) := by
    ext x; rw [Finset.mem_filter, Fintype.mem_piFinset, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ j; have hj1 := h1 j; by_cases hj : j = i
      · subst hj; rw [if_pos rfl, Finset.mem_filter]; exact ⟨hj1, h2⟩
      · rw [if_neg hj]; exact hj1
    · intro h; refine ⟨fun j => ?_, ?_⟩
      · have := h j; by_cases hj : j = i
        · subst hj; rw [if_pos rfl, Finset.mem_filter] at this; exact this.1
        · rw [if_neg hj] at this; exact this
      · have := h i; rw [if_pos rfl, Finset.mem_filter] at this; exact this.2
  rw [heq, Fintype.card_piFinset]
  have hcard : ∀ j : Fin d, (if j = i then ((Finset.Icc (-(n : ℤ)) n).filter (fun v => v + b ∈ Finset.Icc (-(n:ℤ)) n))
        else Finset.Icc (-(n : ℤ)) n).card = (if j = i then (2 * n) else (2 * n + 1)) := by
    intro j; by_cases hj : j = i
    · rw [if_pos hj, if_pos hj]
      rcases hb with h | h <;> subst h
      · rw [show ((Finset.Icc (-(n:ℤ)) n).filter (fun v => v + 1 ∈ Finset.Icc (-(n:ℤ)) n))
              = Finset.Icc (-(n:ℤ)) (n-1) from by
            ext v; rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]; omega,
          Int.card_Icc]; omega
      · rw [show ((Finset.Icc (-(n:ℤ)) n).filter (fun v => v + (-1) ∈ Finset.Icc (-(n:ℤ)) n))
              = Finset.Icc (-(n:ℤ)+1) n from by
            ext v; rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]; omega,
          Int.card_Icc]; omega
    · rw [if_neg hj, if_neg hj, Int.card_Icc]; omega
  rw [Finset.prod_congr rfl (fun j _ => hcard j),
    ← Finset.mul_prod_erase Finset.univ (fun j => if j = i then (2 * n) else (2 * n + 1))
      (Finset.mem_univ i), if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

theorem shiftMap_mem (d n : ℕ) (i : Fin d) (b : ℤ) (hb : b = 1 ∨ b = -1) (x : Site d)
    (hx : x ∈ shiftDom d n i b) : shiftMap d n i b x ∈ edgeAxisI d n i := by
  rw [shiftDom, Finset.mem_filter] at hx
  have hxbox : x ∈ boxSV_boxF d n := hx.1
  rw [boxSV_mem_boxF] at hxbox
  rw [edgeAxisI, Finset.mem_filter, shiftMap, boxSV_mem_edgeF]
  refine ⟨⟨by rw [boxSV_mem_boxF]; exact hxbox, ?_, shift_adj d n i x b hb⟩, ?_⟩
  · rw [boxSV_mem_boxF]; intro j; by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact hx.2
    · simp only [Function.update_of_ne hj]; exact hxbox j
  · simp only [shiftMap, Function.update_self, ne_eq]; rcases hb with h|h <;> subst h <;> omega

theorem shiftMap_inj (d n : ℕ) (i : Fin d) (b : ℤ) : Function.Injective (shiftMap d n i b) :=
  fun x y h => (Prod.ext_iff.mp h).1

theorem edgeAxisI_eq (d n : ℕ) (i : Fin d) :
    edgeAxisI d n i = (shiftDom d n i 1).image (shiftMap d n i 1)
        ∪ (shiftDom d n i (-1)).image (shiftMap d n i (-1)) := by
  ext p
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · intro hp
    rw [edgeAxisI, Finset.mem_filter, boxSV_mem_edgeF] at hp
    obtain ⟨⟨h1box, h2box, hadj⟩, hne⟩ := hp
    rw [hypercubicLattice_adj] at hadj
    rw [boxSV_mem_boxF] at h1box h2box
    have hdiff : (p.1 i - p.2 i).natAbs = 1 := by
      have hge : 1 ≤ (p.1 i - p.2 i).natAbs := by
        rcases Nat.eq_zero_or_pos (p.1 i - p.2 i).natAbs with h | h
        · exact absurd (by omega : p.1 i = p.2 i) hne
        · omega
      have hle : (p.1 i - p.2 i).natAbs ≤ ∑ k, (p.1 k - p.2 k).natAbs :=
        Finset.single_le_sum (f := fun k => (p.1 k - p.2 k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    have hother : ∀ j ≠ i, p.1 j = p.2 j := by
      intro j hj; by_contra hc
      have hjge : 1 ≤ (p.1 j - p.2 j).natAbs := by
        rcases Nat.eq_zero_or_pos (p.1 j - p.2 j).natAbs with h | h
        · exact absurd (by omega : p.1 j = p.2 j) hc
        · omega
      have : (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs ≤ ∑ k, (p.1 k - p.2 k).natAbs := by
        rw [show (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs
              = ∑ k ∈ ({i, j} : Finset (Fin d)), (p.1 k - p.2 k).natAbs from
            (Finset.sum_pair (f := fun k => (p.1 k - p.2 k).natAbs) (Ne.symm hj)).symm]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega
    have hp2 : p.2 = Function.update p.1 i (p.1 i + (p.2 i - p.1 i)) := by
      funext j; by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; ring
      · simp only [Function.update_of_ne hj]; exact (hother j hj).symm
    have hb : p.2 i - p.1 i = 1 ∨ p.2 i - p.1 i = -1 := by omega
    have hpeq : ∀ b : ℤ, p.2 i - p.1 i = b → p = shiftMap d n i b p.1 := by
      intro b hbv; rw [shiftMap]; apply Prod.ext
      · rfl
      · rw [hp2]; simp only; congr 1; omega
    rcases hb with hb | hb
    · left; refine ⟨p.1, ?_, (hpeq 1 hb).symm⟩
      rw [shiftDom, Finset.mem_filter]
      refine ⟨by rw [boxSV_mem_boxF]; exact h1box, ?_⟩
      have hpval : p.1 i + 1 = p.2 i := by omega
      rw [hpval]; exact h2box i
    · right; refine ⟨p.1, ?_, (hpeq (-1) hb).symm⟩
      rw [shiftDom, Finset.mem_filter]
      refine ⟨by rw [boxSV_mem_boxF]; exact h1box, ?_⟩
      have hpval : p.1 i + (-1) = p.2 i := by omega
      rw [hpval]; exact h2box i
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact shiftMap_mem d n i 1 (Or.inl rfl) x hx
    · exact shiftMap_mem d n i (-1) (Or.inr rfl) x hx

theorem fwd_bwd_disjoint (d n : ℕ) (i : Fin d) :
    Disjoint ((shiftDom d n i 1).image (shiftMap d n i 1))
        ((shiftDom d n i (-1)).image (shiftMap d n i (-1))) := by
  rw [Finset.disjoint_left]
  rintro p hp1 hp2
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨x, hx, rfl⟩ := hp1
  obtain ⟨y, hy, hxy⟩ := hp2
  rw [shiftMap, shiftMap, Prod.ext_iff] at hxy
  obtain ⟨h1, h2⟩ := hxy
  subst h1
  have := congrFun h2 i
  simp only [Function.update_self] at this
  omega

theorem card_edgeAxisI (d n : ℕ) (i : Fin d) (hd : 1 ≤ d) :
    (edgeAxisI d n i).card = 2 * ((2 * n) * (2 * n + 1) ^ (d - 1)) := by
  rw [edgeAxisI_eq, Finset.card_union_of_disjoint (fwd_bwd_disjoint d n i),
    Finset.card_image_of_injective _ (shiftMap_inj d n i 1),
    Finset.card_image_of_injective _ (shiftMap_inj d n i (-1)),
    card_shiftDom d n i 1 (Or.inl rfl) hd, card_shiftDom d n i (-1) (Or.inr rfl) hd]
  ring

theorem edgeF_biUnion (d n : ℕ) :
    (boxSV_edgeF d n) = Finset.univ.biUnion (fun i : Fin d => edgeAxisI d n i) := by
  ext p; rw [Finset.mem_biUnion]
  constructor
  · intro hp
    have hadj := (boxSV_mem_edgeF.mp hp).2.2
    rw [hypercubicLattice_adj] at hadj
    obtain ⟨i, hi⟩ : ∃ i, (p.1 i - p.2 i).natAbs ≠ 0 := by
      by_contra hc; push_neg at hc; simp only [hc] at hadj; simp at hadj
    exact ⟨i, Finset.mem_univ i, by rw [edgeAxisI, Finset.mem_filter]; exact ⟨hp, fun he => hi (by rw [he]; simp)⟩⟩
  · rintro ⟨i, _, hp⟩; rw [edgeAxisI, Finset.mem_filter] at hp; exact hp.1

theorem edgeAxis_disjoint (d n : ℕ) (i j : Fin d) (hij : i ≠ j) :
    Disjoint (edgeAxisI d n i) (edgeAxisI d n j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [edgeAxisI, Finset.mem_filter] at hpi hpj
  have hadj := (boxSV_mem_edgeF.mp hpi.1).2.2
  rw [hypercubicLattice_adj] at hadj
  have hi : 1 ≤ (p.1 i - p.2 i).natAbs := by
    rcases Nat.eq_zero_or_pos (p.1 i - p.2 i).natAbs with h | h
    · exact absurd (by omega : p.1 i = p.2 i) hpi.2
    · omega
  have hj : 1 ≤ (p.1 j - p.2 j).natAbs := by
    rcases Nat.eq_zero_or_pos (p.1 j - p.2 j).natAbs with h | h
    · exact absurd (by omega : p.1 j = p.2 j) hpj.2
    · omega
  have hsum : (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs ≤ ∑ k, (p.1 k - p.2 k).natAbs := by
    rw [show (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs
          = ∑ k ∈ ({i, j} : Finset (Fin d)), (p.1 k - p.2 k).natAbs from
        (Finset.sum_pair (f := fun k => (p.1 k - p.2 k).natAbs) hij).symm]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

theorem edgeCard_eq (d n : ℕ) (hd : 1 ≤ d) :
    boxSV_edgeCard d n = d * (2 * ((2 * n) * (2 * n + 1) ^ (d - 1))) := by
  unfold boxSV_edgeCard
  rw [edgeF_biUnion, Finset.card_biUnion (fun i _ j _ hij => edgeAxis_disjoint d n i j hij),
    Finset.sum_congr rfl (fun i _ => card_edgeAxisI d n i hd),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring


theorem boxGraph_edgeCard (d n : ℕ) (hd : 1 ≤ d) :
    (boxGraph d n).edgeFinset.card = d * ((2 * n) * (2 * n + 1) ^ (d - 1)) := by
  have h := fup_edge_card_eq d n
  rw [edgeCard_eq d n hd] at h
  set Z := d * ((2 * n) * (2 * n + 1) ^ (d - 1)) with hZ
  have h2 : d * (2 * ((2 * n) * (2 * n + 1) ^ (d - 1))) = 2 * Z := by rw [hZ]; ring
  rw [h2] at h
  omega

end EdgeCount
end FK
end StatMech
