/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing
    (R : FKRectTorus) (n : Nat)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    IsIncreasing
      (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) := by
  intro omega tau hot hconn
  apply hconn.mono
  apply fkRectOpenGraph_mono R
  intro e he
  have hle := hot e
  rw [he] at hle
  exact top_le_iff.mp hle

theorem fkRectDevelopedSquareEndpointConnection_subset_torus
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    fkRectDevelopedSquareEndpointConnectionEvent R n p ⊆
      fkRectDevelopedSquareTorusEndpointConnectionEvent R n p := by
  intro omega hconn
  exact fkRectDevelopedSquareEndpointConnection_imp_torusReachable
    R n hwidth hheight omega p hconn

theorem fkRectDevelopedSquareHorizontalCrossingEvent_eq_endpointUnion
    (R : FKRectTorus) (n : Nat) :
    fkRectDevelopedSquareHorizontalCrossingEvent R n =
      fkRectFiniteEventUnion
        (fkRectDevelopedSquareHorizontalEndpointPairs n)
        (fkRectDevelopedSquareEndpointConnectionEvent R n) := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    let p : (StatMech.RSW.Box.rect 0 n 0 n) ×
        (StatMech.RSW.Box.rect 0 n 0 n) :=
      (⟨x.1, x.2.1⟩, ⟨y.1, y.2.1⟩)
    refine ⟨p, ?_, ?_⟩
    · classical
      simp [fkRectDevelopedSquareHorizontalEndpointPairs, p,
        x.2.2, y.2.2]
    · simpa [fkRectDevelopedSquareEndpointConnectionEvent, p] using hxy
  · rintro ⟨p, hp, hxy⟩
    have hend : p.1.1 0 = 0 ∧ p.2.1 0 = n := by
      classical
      simpa [fkRectDevelopedSquareHorizontalEndpointPairs] using hp
    refine ⟨⟨p.1.1, p.1.2, hend.1⟩,
      ⟨p.2.1, p.2.2, hend.2⟩, ?_⟩
    simpa [fkRectDevelopedSquareEndpointConnectionEvent] using hxy

theorem fkRectDevelopedSquareVerticalCrossingEvent_eq_endpointUnion
    (R : FKRectTorus) (n : Nat) :
    fkRectDevelopedSquareVerticalCrossingEvent R n =
      fkRectFiniteEventUnion
        (fkRectDevelopedSquareVerticalEndpointPairs n)
        (fkRectDevelopedSquareEndpointConnectionEvent R n) := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    let p : (StatMech.RSW.Box.rect 0 n 0 n) ×
        (StatMech.RSW.Box.rect 0 n 0 n) :=
      (⟨x.1, x.2.1⟩, ⟨y.1, y.2.1⟩)
    refine ⟨p, ?_, ?_⟩
    · classical
      simp [fkRectDevelopedSquareVerticalEndpointPairs, p,
        x.2.2, y.2.2]
    · simpa [fkRectDevelopedSquareEndpointConnectionEvent, p] using hxy
  · rintro ⟨p, hp, hxy⟩
    have hend : p.1.1 1 = 0 ∧ p.2.1 1 = n := by
      classical
      simpa [fkRectDevelopedSquareVerticalEndpointPairs] using hp
    refine ⟨⟨p.1.1, p.1.2, hend.1⟩,
      ⟨p.2.1, p.2.2, hend.2⟩, ?_⟩
    simpa [fkRectDevelopedSquareEndpointConnectionEvent] using hxy

theorem fkRectDevelopedSquareHorizontalEndpointPairs_nonempty (n : Nat) :
    (fkRectDevelopedSquareHorizontalEndpointPairs n).Nonempty := by
  classical
  let x : Site 2 := ![0, 0]
  let y : Site 2 := ![(n : Int), 0]
  have hx : x ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, x]
  have hy : y ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, y]
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
  simp [fkRectDevelopedSquareHorizontalEndpointPairs, x, y]

theorem fkRectDevelopedSquareVerticalEndpointPairs_nonempty (n : Nat) :
    (fkRectDevelopedSquareVerticalEndpointPairs n).Nonempty := by
  classical
  let x : Site 2 := ![0, 0]
  let y : Site 2 := ![0, (n : Int)]
  have hx : x ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, x]
  have hy : y ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, y]
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
  simp [fkRectDevelopedSquareVerticalEndpointPairs, x, y]


theorem fkRectDevelopedSquareHorizontalEndpointPairs_card_le (n : Nat) :
    (fkRectDevelopedSquareHorizontalEndpointPairs n).card ≤ (n + 1) ^ 2 := by
  classical
  let encode : {p // p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n} →
      Fin (n + 1) × Fin (n + 1) := fun p =>
    (⟨Int.toNat (p.1.1.1 1), by
        have hp := p.1.1.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩,
      ⟨Int.toNat (p.1.2.1 1), by
        have hp := p.1.2.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩)
  have hinj : Function.Injective encode := by
    intro p r hpr
    have hpEnds : p.1.1.1 0 = 0 ∧ p.1.2.1 0 = n := by
      exact (mem_fkRectDevelopedSquareHorizontalEndpointPairs n p.1).mp p.2
    have hrEnds : r.1.1.1 0 = 0 ∧ r.1.2.1 0 = n := by
      exact (mem_fkRectDevelopedSquareHorizontalEndpointPairs n r.1).mp r.2
    have hfirst : Int.toNat (p.1.1.1 1) =
        Int.toNat (r.1.1.1 1) :=
      congrArg (fun z => z.1.val) hpr
    have hsecond : Int.toNat (p.1.2.1 1) =
        Int.toNat (r.1.2.1 1) :=
      congrArg (fun z => z.2.val) hpr
    have hp1 := p.1.1.2
    have hp2 := p.1.2.2
    have hr1 := r.1.1.2
    have hr2 := r.1.2.2
    rw [StatMech.RSW.Box.mem_rect] at hp1 hp2 hr1 hr2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · exact hpEnds.1.trans hrEnds.1.symm
      · calc
          p.1.1.1 1 = (Int.toNat (p.1.1.1 1) : Int) :=
            (Int.toNat_of_nonneg hp1.2.2.1).symm
          _ = (Int.toNat (r.1.1.1 1) : Int) := by exact_mod_cast hfirst
          _ = r.1.1.1 1 := Int.toNat_of_nonneg hr1.2.2.1
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · exact hpEnds.2.trans hrEnds.2.symm
      · calc
          p.1.2.1 1 = (Int.toNat (p.1.2.1 1) : Int) :=
            (Int.toNat_of_nonneg hp2.2.2.1).symm
          _ = (Int.toNat (r.1.2.1 1) : Int) := by exact_mod_cast hsecond
          _ = r.1.2.1 1 := Int.toNat_of_nonneg hr2.2.2.1
  rw [← Fintype.card_coe]
  calc
    Fintype.card {p // p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n} ≤
        Fintype.card (Fin (n + 1) × Fin (n + 1)) :=
      Fintype.card_le_of_injective encode hinj
    _ = (n + 1) ^ 2 := by simp [pow_two]


theorem fkRectDevelopedSquareVerticalEndpointPairs_card_le (n : Nat) :
    (fkRectDevelopedSquareVerticalEndpointPairs n).card ≤ (n + 1) ^ 2 := by
  classical
  let encode : {p // p ∈ fkRectDevelopedSquareVerticalEndpointPairs n} →
      Fin (n + 1) × Fin (n + 1) := fun p =>
    (⟨Int.toNat (p.1.1.1 0), by
        have hp := p.1.1.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩,
      ⟨Int.toNat (p.1.2.1 0), by
        have hp := p.1.2.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩)
  have hinj : Function.Injective encode := by
    intro p r hpr
    have hpEnds : p.1.1.1 1 = 0 ∧ p.1.2.1 1 = n := by
      exact (mem_fkRectDevelopedSquareVerticalEndpointPairs n p.1).mp p.2
    have hrEnds : r.1.1.1 1 = 0 ∧ r.1.2.1 1 = n := by
      exact (mem_fkRectDevelopedSquareVerticalEndpointPairs n r.1).mp r.2
    have hfirst : Int.toNat (p.1.1.1 0) =
        Int.toNat (r.1.1.1 0) :=
      congrArg (fun z => z.1.val) hpr
    have hsecond : Int.toNat (p.1.2.1 0) =
        Int.toNat (r.1.2.1 0) :=
      congrArg (fun z => z.2.val) hpr
    have hp1 := p.1.1.2
    have hp2 := p.1.2.2
    have hr1 := r.1.1.2
    have hr2 := r.1.2.2
    rw [StatMech.RSW.Box.mem_rect] at hp1 hp2 hr1 hr2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · calc
          p.1.1.1 0 = (Int.toNat (p.1.1.1 0) : Int) :=
            (Int.toNat_of_nonneg hp1.1).symm
          _ = (Int.toNat (r.1.1.1 0) : Int) := by exact_mod_cast hfirst
          _ = r.1.1.1 0 := Int.toNat_of_nonneg hr1.1
      · exact hpEnds.1.trans hrEnds.1.symm
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · calc
          p.1.2.1 0 = (Int.toNat (p.1.2.1 0) : Int) :=
            (Int.toNat_of_nonneg hp2.1).symm
          _ = (Int.toNat (r.1.2.1 0) : Int) := by exact_mod_cast hsecond
          _ = r.1.2.1 0 := Int.toNat_of_nonneg hr2.1
      · exact hpEnds.2.trans hrEnds.2.symm
  rw [← Fintype.card_coe]
  calc
    Fintype.card {p // p ∈ fkRectDevelopedSquareVerticalEndpointPairs n} ≤
        Fintype.card (Fin (n + 1) × Fin (n + 1)) :=
      Fintype.card_le_of_injective encode hinj
    _ = (n + 1) ^ 2 := by simp [pow_two]


theorem fkRectDevelopedSquare_exists_endpoint_connection_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareHorizontalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareVerticalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_direction_crossing_ge
      R n hn hwidth hheight hq with hhorizontal | hvertical
  · left
    rw [fkRectDevelopedSquareHorizontalCrossingEvent_eq_endpointUnion]
      at hhorizontal
    exact exists_card_mul_eventMass_ge_of_finiteUnion_ge R
      (zero_lt_one.trans_le hq)
      (fkRectDevelopedSquareHorizontalEndpointPairs_nonempty n)
      (fkRectDevelopedSquareEndpointConnectionEvent R n) hhorizontal
  · right
    rw [fkRectDevelopedSquareVerticalCrossingEvent_eq_endpointUnion]
      at hvertical
    exact exists_card_mul_eventMass_ge_of_finiteUnion_ge R
      (zero_lt_one.trans_le hq)
      (fkRectDevelopedSquareVerticalEndpointPairs_nonempty n)
      (fkRectDevelopedSquareEndpointConnectionEvent R n) hvertical


theorem fkRectDevelopedSquare_exists_torus_endpoint_connection_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareHorizontalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareVerticalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_endpoint_connection_ge
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_left
    · exact fkRectCriticalEventMass_mono R
        (zero_lt_one.trans_le hq)
        (fkRectDevelopedSquareEndpointConnection_subset_torus
          R n hwidth hheight p)
    · positivity
  · right
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_left
    · exact fkRectCriticalEventMass_mono R
        (zero_lt_one.trans_le hq)
        (fkRectDevelopedSquareEndpointConnection_subset_torus
          R n hwidth hheight p)
    · positivity


theorem fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_polynomial
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q)) ≤ ((n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤ ((n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_torus_endpoint_connection_ge
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast
        fkRectDevelopedSquareHorizontalEndpointPairs_card_le n
    · exact fkRectCriticalEventMass_nonneg R
        (zero_lt_one.trans_le hq) _
  · right
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast fkRectDevelopedSquareVerticalEndpointPairs_card_le n
    · exact fkRectCriticalEventMass_nonneg R
        (zero_lt_one.trans_le hq) _


theorem fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_div
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) ≤
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) ≤
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  have hk : (0 : Real) < (((n + 1) ^ 2 : Nat) : Real) := by positivity
  have hqden : (0 : Real) < 2 * (1 + q) := by positivity
  have hreassoc :
      1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) =
        (1 / (2 * (1 + q))) / (((n + 1) ^ 2 : Nat) : Real) := by
    field_simp
  rcases fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_polynomial
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, ?_⟩
    rw [hreassoc, div_le_iff₀ hk]
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, mul_comm] using hlower
  · right
    refine ⟨p, hp, ?_⟩
    rw [hreassoc, div_le_iff₀ hk]
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, mul_comm] using hlower


theorem fkRectDevelopedSquare_exists_fkg_attached_torus_endpoint
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) (B : Set R.Configuration)
    (hB : IsIncreasing B) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      (1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real))) *
          fkRectCriticalEventMass R q B ≤
        fkRectCriticalEventMass R q
          (B ∩ fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      (1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real))) *
          fkRectCriticalEventMass R q B ≤
        fkRectCriticalEventMass R q
          (B ∩ fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_div
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, ?_⟩
    calc
      _ ≤ fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) *
            fkRectCriticalEventMass R q B :=
        mul_le_mul_of_nonneg_right hlower
          (fkRectCriticalEventMass_nonneg R
            (zero_lt_one.trans_le hq) B)
      _ = fkRectCriticalEventMass R q B *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) :=
        mul_comm _ _
      _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
        (fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing
          R n p)
  · right
    refine ⟨p, hp, ?_⟩
    calc
      _ ≤ fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) *
            fkRectCriticalEventMass R q B :=
        mul_le_mul_of_nonneg_right hlower
          (fkRectCriticalEventMass_nonneg R
            (zero_lt_one.trans_le hq) B)
      _ = fkRectCriticalEventMass R q B *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) :=
        mul_comm _ _
      _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
        (fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing
          R n p)

end
end StatMech.FrontierD
