/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part7
open Finset Matrix


namespace StatMech.FrontierD

theorem svHorizontalIsC_iff_ne {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (i : Fin N) : svHorizontalIsC hN h i ↔ x i ≠ y i := by
  have hs := svHorizontalIce_step hN hice i
  unfold svHorizontalIsC
  cases hx : x i <;> cases hy : y i <;>
    cases hp : h (SixVertexArrows.cyclicPred hN i) <;>
    cases hh : h i <;> simp [hx, hy, hp, hh] at hs ⊢

theorem svHorizontalLocalWeight_of_ice {N : Nat} (hN : 0 < N)
    (c : Real) {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (i : Fin N) :
    svHorizontalLocalWeight hN c x y h i = if x i ≠ y i then c else 1 := by
  classical
  unfold svHorizontalLocalWeight
  rw [if_pos (hice i)]
  rw [if_congr (svHorizontalIsC_iff_ne hN hice i) rfl rfl]

theorem svHorizontalRowWeight_of_ice {N : Nat} (hN : 0 < N)
    (c : Real) {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h) :
    svHorizontalRowWeight hN c x y h = c ^ sixVertexRowDistance x y := by
  unfold svHorizontalRowWeight sixVertexRowDistance
  simp_rw [svHorizontalLocalWeight_of_ice hN c hice]
  rw [Finset.prod_ite]
  simp

theorem svHorizontalRowWeight_eq_zero_of_not_ice {N : Nat} (hN : 0 < N)
    (c : Real) {x y h : SixVertexRow N} (hice : ¬svHorizontalIce hN x y h) :
    svHorizontalRowWeight hN c x y h = 0 := by
  simp only [svHorizontalIce, not_forall] at hice
  obtain ⟨i, hi⟩ := hice
  unfold svHorizontalRowWeight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold svHorizontalLocalWeight
  rw [if_neg hi]

open Classical in
theorem svHorizontalRowWeight_sum_formula {N : Nat} (hN : 0 < N)
    (c : Real) (x y : SixVertexRow N)
    (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    (∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h) =
      (if svRowPrefixForward x y then c ^ sixVertexRowDistance x y else 0) +
      (if svRowPrefixForward y x then c ^ sixVertexRowDistance x y else 0) := by
  classical
  let P : Bool → Prop := fun b =>
    if b then svRowPrefixForward y x else svRowPrefixForward x y
  letI : Fintype {b : Bool // P b} := Fintype.ofFinite _
  let e := svHorizontalIceEquivBool hN x y hcount
  have hfilter :
      (∑ h : {h : SixVertexRow N // svHorizontalIce hN x y h},
        svHorizontalRowWeight hN c x y h.1) =
      ∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun h : SixVertexRow N => svHorizontalIce hN x y h)
      (by simp)]
    apply Finset.sum_filter_of_ne
    intro h _ hweight
    by_contra hnot
    exact hweight (svHorizontalRowWeight_eq_zero_of_not_ice hN c hnot)
  rw [← hfilter]
  calc
    (∑ h : {h : SixVertexRow N // svHorizontalIce hN x y h},
        svHorizontalRowWeight hN c x y h.1) =
      ∑ b : {b : Bool // P b},
        svHorizontalRowWeight hN c x y (e.symm b).1 := by
          exact (e.symm.sum_comp _).symm
    _ = ∑ _b : {b : Bool // P b}, c ^ sixVertexRowDistance x y := by
      apply Fintype.sum_congr
      intro b
      exact svHorizontalRowWeight_of_ice hN c (e.symm b).2
    _ = (if svRowPrefixForward x y then c ^ sixVertexRowDistance x y else 0) +
        (if svRowPrefixForward y x then c ^ sixVertexRowDistance x y else 0) := by
      have hsub := Finset.sum_subtype (p := P) (F := inferInstance)
        (Finset.univ.filter P)
        (by intro b; simp [P])
        (fun _b : Bool => c ^ sixVertexRowDistance x y)
      rw [← hsub]
      have hcardFalse :
          #{b ∈ (Finset.univ : Finset Bool) | b = false} = 1 := by
        rw [show ({b ∈ (Finset.univ : Finset Bool) | b = false}) = {false} by
          ext b
          cases b <;> simp]
        simp
      have hcardTrue :
          #{b ∈ (Finset.univ : Finset Bool) | b = true} = 1 := by
        rw [show ({b ∈ (Finset.univ : Finset Bool) | b = true}) = {true} by
          ext b
          cases b <;> simp]
        simp
      have htf : ({true, false} : Finset Bool) = Finset.univ := by
        ext b
        cases b <;> simp
      have hcardFalse' :
          #{b ∈ ({true, false} : Finset Bool) | b = false} = 1 := by
        rw [htf]
        exact hcardFalse
      have hcardTrue' :
          #{b ∈ ({true, false} : Finset Bool) | b = true} = 1 := by
        rw [htf]
        exact hcardTrue
      by_cases hxy : svRowPrefixForward x y <;>
        by_cases hyx : svRowPrefixForward y x <;>
        norm_num [P, hxy, hyx, hcardFalse, hcardTrue,
          hcardFalse', hcardTrue']; ring

theorem svRowPrefixForward_self {N : Nat} (x : SixVertexRow N) :
    svRowPrefixForward x x := by
  intro k
  omega

theorem svHorizontalRowWeight_sum_eq_transfer {N : Nat} (hN : 0 < N)
    (c : Real) (x y : SixVertexRow N) :
    (∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h) =
      sixVertexTransfer N c x y := by
  classical
  by_cases hcount : sixVertexUpCount x = sixVertexUpCount y
  · rw [svHorizontalRowWeight_sum_formula hN c x y hcount]
    by_cases hxy : x = y
    · subst y
      simp [sixVertexTransfer, svRowPrefixForward_self, sixVertexRowDistance]
      norm_num
    · by_cases hinter : SixVertexInterlaced x y
      · rcases hinter with hforward | hbackward
        · have hpref : svRowPrefixForward x y :=
            (svForwardInterlaced_iff_prefix x y hcount).1 hforward
          have hinter' : SixVertexInterlaced x y := Or.inl hforward
          have hnback : ¬svRowPrefixForward y x := by
            intro hback
            exact hxy (svRowPrefixForward_antisymm hpref hback)
          simp [sixVertexTransfer, hxy, hinter', hpref, hnback]
        · have hpref : svRowPrefixForward y x :=
            (svForwardInterlaced_iff_prefix y x hcount.symm).1 hbackward
          have hinter' : SixVertexInterlaced x y := Or.inr hbackward
          have hnforward : ¬svRowPrefixForward x y := by
            intro hfor
            exact hxy (svRowPrefixForward_antisymm hfor hpref)
          simp [sixVertexTransfer, hxy, hinter', hpref, hnforward]
      · have hnforward : ¬svRowPrefixForward x y := by
          intro hpref
          apply hinter
          exact Or.inl ((svForwardInterlaced_iff_prefix x y hcount).2 hpref)
        have hnback : ¬svRowPrefixForward y x := by
          intro hpref
          apply hinter
          exact Or.inr ((svForwardInterlaced_iff_prefix y x hcount.symm).2 hpref)
        simp [sixVertexTransfer, hxy, hinter, hnforward, hnback]
  · have hzero (h : SixVertexRow N) :
        svHorizontalRowWeight hN c x y h = 0 := by
      apply svHorizontalRowWeight_eq_zero_of_not_ice
      intro hice
      exact hcount (svHorizontalIce_upCount_eq hN hice)
    simp_rw [hzero]
    simp [sixVertexTransfer_eq_zero_of_upCount_ne c hcount]

theorem svFinitePeriodicSucc_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (finitePeriodicSucc hN) := by
  intro i j hij
  apply Fin.ext
  have hijv := congrArg Fin.val hij
  change (i.val + 1) % N = (j.val + 1) % N at hijv
  by_cases hi : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hi] at hijv
    by_cases hj : j.val + 1 < N
    · rw [Nat.mod_eq_of_lt hj] at hijv
      omega
    · have hjeq : j.val + 1 = N := by omega
      rw [hjeq, Nat.mod_self] at hijv
      omega
  · have hieq : i.val + 1 = N := by omega
    rw [hieq, Nat.mod_self] at hijv
    by_cases hj : j.val + 1 < N
    · rw [Nat.mod_eq_of_lt hj] at hijv
      omega
    · omega

end StatMech.FrontierD
