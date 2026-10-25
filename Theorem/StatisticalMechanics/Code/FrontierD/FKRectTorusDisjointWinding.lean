/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace FKRectDartListUsesPoint

variable {L : Nat}

theorem of_mem {l : List (ons_Dart L)} {d : ons_Dart L}
    (hd : d ∈ l) :
    FKRectDartListUsesPoint l d.1 :=
  ⟨d, hd, Or.inl rfl⟩

theorem of_mem_end {l : List (ons_Dart L)} {d : ons_Dart L}
    (hd : d ∈ l) :
    FKRectDartListUsesPoint l (ons_dirStep L d.2 d.1) :=
  ⟨d, hd, Or.inr rfl⟩

theorem exists_ne_zero_of_sum_ne_zero
    (f : ons_Dart L → Int) {l : List (ons_Dart L)}
    (h : (l.map f).sum ≠ 0) :
    ∃ d ∈ l, f d ≠ 0 := by
  contrapose! h
  exact List.sum_eq_zero (fun z hz => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hz
    exact h d hd)

theorem of_horizontal_ne_zero {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l p := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartHorizontal d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · have hp : (x, y) = p := by
      have hp' : p = (x, y) := by
        simpa [IntegralSquareTorusCycle.dartHorizontal,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    exact ⟨((x, y), 0), hd, Or.inl hp⟩
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne
  · have hp : (x - 1, y) = p := by
      have hp' : p = (x - 1, y) := by
        simpa [IntegralSquareTorusCycle.dartHorizontal,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    refine ⟨((x, y), 2), hd, Or.inr ?_⟩
    simpa [ons_dirStep] using hp
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne

theorem of_vertical_ne_zero {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l p := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartVertical d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : (x, y) = p := by
      have hp' : p = (x, y) := by
        simpa [IntegralSquareTorusCycle.dartVertical,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    exact ⟨((x, y), 1), hd, Or.inl hp⟩
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : (x, y - 1) = p := by
      have hp' : p = (x, y - 1) := by
        simpa [IntegralSquareTorusCycle.dartVertical,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    refine ⟨((x, y), 3), hd, Or.inr ?_⟩
    simpa [ons_dirStep] using hp

theorem of_horizontal_ne_zero_east {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l (p.1 + 1, p.2) := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartHorizontal d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · have hp : p = (x, y) := by
      simpa [IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 0), hd, Or.inr ?_⟩
    rw [hp]
    simp [ons_dirStep]
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne
  · have hp : p = (x - 1, y) := by
      simpa [IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 2), hd, Or.inl ?_⟩
    rw [hp]
    apply Prod.ext <;> simp
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne

theorem of_vertical_ne_zero_north {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l (p.1, p.2 + 1) := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartVertical d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : p = (x, y) := by
      simpa [IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 1), hd, Or.inr ?_⟩
    rw [hp]
    simp [ons_dirStep]
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : p = (x, y - 1) := by
      simpa [IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 3), hd, Or.inl ?_⟩
    rw [hp]
    apply Prod.ext <;> simp

end FKRectDartListUsesPoint


theorem IntegralSquareTorusCycle.ofDartList_locallyDisjoint
    {L : Nat} [Fact (2 < L)]
    (v w : List (ons_Dart L))
    (hv : IntegralSquareTorusCycle.DartListBalanced v)
    (hw : IntegralSquareTorusCycle.DartListBalanced w)
    (hdisj : ∀ p, FKRectDartListUsesPoint v p →
      ¬ FKRectDartListUsesPoint w p) :
    (IntegralSquareTorusCycle.ofDartList v hv).LocallyDisjoint
      (IntegralSquareTorusCycle.ofDartList w hw) := by
  intro p
  by_cases hC :
      (IntegralSquareTorusCycle.ofDartList v hv).horizontal p = 0 ∧
        (IntegralSquareTorusCycle.ofDartList v hv).vertical p = 0
  · exact Or.inl hC
  · right
    constructor
    · by_contra hwest
      have hCuses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hC with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hWuses : FKRectDartListUsesPoint w p := by
        have h := FKRectDartListUsesPoint.of_horizontal_ne_zero_east
          (l := w) hwest
        simpa using h
      exact hdisj p hCuses hWuses
    · by_contra hsouth
      have hCuses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hC with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hWuses : FKRectDartListUsesPoint w p := by
        have h := FKRectDartListUsesPoint.of_vertical_ne_zero_north
          (l := w) hsouth
        simpa using h
      exact hdisj p hCuses hWuses


theorem fkRectSquareRepresentativeVertex_eq_of_pointMod_eq
    (R : FKRectTorus) {a b : Int × Int}
    (hmod : fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) a =
      fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) b) :
    fkRectSquareRepresentativeVertex R a =
      fkRectSquareRepresentativeVertex R b := by
  let L := fkRectSquareCoverSide R
  have hxcast : (a.1 : ZMod L) = (b.1 : ZMod L) := by
    exact congrArg Prod.fst hmod
  have hycast : (a.2 : ZMod L) = (b.2 : ZMod L) := by
    exact congrArg Prod.snd hmod
  have hxdiv : (L : Int) ∣ b.1 - a.1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a.1 b.1 L).mp hxcast
  have hydiv : (L : Int) ∣ b.2 - a.2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a.2 b.2 L).mp hycast
  obtain ⟨A, hA⟩ := hxdiv
  obtain ⟨B, hB⟩ := hydiv
  let alpha : Int := -A
  let beta : Int := -B
  let u : Int × Int :=
    ((R.height / 2 : Nat) * (alpha + beta),
      (R.width : Int) * (alpha - beta))
  have hheight : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast Nat.two_mul_div_two_of_even R.height_even
  have hLcast : (L : Int) = (R.width : Int) * R.height := by
    simp [L, fkRectSquareCoverSide]
  have hA' : a.1 - b.1 =
      (R.width : Int) * R.height * (-A) := by
    calc
      a.1 - b.1 = -(b.1 - a.1) := by ring
      _ = -((L : Int) * A) := by rw [hA]
      _ = (R.width : Int) * R.height * (-A) := by
        rw [hLcast]
        ring
  have hB' : a.2 - b.2 =
      (R.width : Int) * R.height * (-B) := by
    calc
      a.2 - b.2 = -(b.2 - a.2) := by ring
      _ = -((L : Int) * B) := by rw [hB]
      _ = (R.width : Int) * R.height * (-B) := by
        rw [hLcast]
        ring
  have hdeck : fkRectSquareDeckTranslation R u = a - b := by
    apply Prod.ext
    · simp only [fkRectSquareDeckTranslation, u,
        Prod.fst_sub, alpha, beta]
      calc
        (R.width : Int) * ((R.height / 2 : Nat) * (-A + -B)) +
              (R.height / 2 : Nat) * ((R.width : Int) * (-A - -B)) =
            (R.width : Int) * R.height * (-A) := by
              rw [← hheight]
              ring
        _ = a.1 - b.1 := hA'.symm
    · simp only [fkRectSquareDeckTranslation, u,
        Prod.snd_sub, alpha, beta]
      calc
        (R.width : Int) * ((R.height / 2 : Nat) * (-A + -B)) -
              (R.height / 2 : Nat) * ((R.width : Int) * (-A - -B)) =
            (R.width : Int) * R.height * (-B) := by
              rw [← hheight]
              ring
        _ = a.2 - b.2 := hB'.symm
  apply fkRectVertexSquareClass_injective R
  rw [fkRectVertexSquareClass_representative,
    fkRectVertexSquareClass_representative]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact (mem_fkRectSquareDeckLattice_iff R _).mpr ⟨u, hdeck⟩


theorem fkRectSquareRepresentativeVertex_add_deck
    (R : FKRectTorus) (z u : Int × Int) :
    fkRectSquareRepresentativeVertex R
        (z + fkRectSquareDeckTranslation R u) =
      fkRectSquareRepresentativeVertex R z := by
  apply fkRectVertexSquareClass_injective R
  rw [fkRectVertexSquareClass_representative,
    fkRectVertexSquareClass_representative]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (mem_fkRectSquareDeckLattice_iff R _).mpr
  refine ⟨u, ?_⟩
  apply Prod.ext <;> simp


theorem FKRectSquareWalkLift.exists_supportedIntegralDartPath
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧
      ∀ d ∈ l,
        fkRectSquareRepresentativeVertex R d.1 ∈ w.support ∧
        fkRectSquareRepresentativeVertex R
          (fkRectIntegralSquareDartEnd d) ∈ w.support := by
  induction h with
  | nil p hp =>
      exact ⟨[], FKRectIntegralSquareDartPath.nil _, by simp⟩
  | @cons x y z hxy w p q r hp hq hdisp haxis tail ih =>
      obtain ⟨l, hl, hsupp⟩ := ih
      obtain ⟨mu, hmu⟩ := haxis.exists_direction
      refine ⟨(fkRectSquareDevelopPoint p, mu) :: l,
        FKRectIntegralSquareDartPath.cons _ hmu hl, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · constructor
        · rw [fkRectSquareRepresentativeVertex_developPoint, hp]
          simp
        · rw [hmu, fkRectSquareRepresentativeVertex_developPoint, hq]
          simp
      · obtain ⟨hstart, hend⟩ := hsupp d hd
        constructor
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem x hstart
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem x hend


end
end StatMech.FrontierD
