/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part32


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWalkCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWalkCast h p).support = p.support := by
  subst H
  rfl

@[simp] theorem fkIsingSquareWalkCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWalkCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl

theorem fkIsingSquare_closed_west_south_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    [(.dart (e, .west) : FKIsingSquareMedialCarrier n), .dart (e, .south)] <:+:
      fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .west rfl h

theorem fkIsingSquare_closed_east_north_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    [(.dart (e, .east) : FKIsingSquareMedialCarrier n), .dart (e, .north)] <:+:
      fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self,
    fkIsingSquareSideCorner] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .east rfl h

theorem fkIsingSquare_open_west_north_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    [(.dart (e, .west) : FKIsingSquareMedialCarrier n), .dart (e, .north)] <:+:
      fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .west rfl h

theorem fkIsingSquare_open_east_south_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    [(.dart (e, .east) : FKIsingSquareMedialCarrier n), .dart (e, .south)] <:+:
      fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self,
    fkIsingSquareSideCorner] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .east rfl h


theorem fkIsingSquare_double_visit_closed_order
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let p := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
    p.idxOf (.dart (e, .south)) < p.idxOf (.dart (e, .east)) ∨
      p.idxOf (.dart (e, .north)) < p.idxOf (.dart (e, .west)) := by
  let p := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  have hWS := fkIsingSquare_closed_west_south_oriented_infix
    n hn omega e hwest
  have hEN := fkIsingSquare_closed_east_north_oriented_infix
    n hn omega e heast
  have hiWS := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hWS
  have hiEN := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hEN
  have hWmem : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈ p := by
    simpa [p, fkIsingSquarePathUsesLocalSide] using hwest
  have hne : p.idxOf (.dart (e, .west)) ≠ p.idxOf (.dart (e, .east)) := by
    intro hi
    have heq := (List.idxOf_inj hWmem).mp hi
    simp at heq
  have hSmem : (.dart (e, .south) : FKIsingSquareMedialCarrier n) ∈ p :=
    hWS.mem (by simp)
  have hSE : p.idxOf (.dart (e, .south)) ≠
      p.idxOf (.dart (e, .east)) := by
    intro hi
    have heq := (List.idxOf_inj hSmem).mp hi
    simp at heq
  have hNmem : (.dart (e, .north) : FKIsingSquareMedialCarrier n) ∈ p :=
    hEN.mem (by simp)
  have hNW : p.idxOf (.dart (e, .north)) ≠
      p.idxOf (.dart (e, .west)) := by
    intro hi
    have heq := (List.idxOf_inj hNmem).mp hi
    simp at heq
  change p.idxOf (.dart (e, .south)) < p.idxOf (.dart (e, .east)) ∨
    p.idxOf (.dart (e, .north)) < p.idxOf (.dart (e, .west))
  change p.idxOf (.dart (e, .south)) = p.idxOf (.dart (e, .west)) + 1 at hiWS
  change p.idxOf (.dart (e, .north)) = p.idxOf (.dart (e, .east)) + 1 at hiEN
  omega


theorem fkIsingSquare_double_visit_open_pair_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (_hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (_heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) := by
  classical
  let W := fkIsingSquarePathUsesLocalSide n hn
    (setOpen e.1 omega) e .west
  let E := fkIsingSquarePathUsesLocalSide n hn
    (setOpen e.1 omega) e .east
  have hWN := fkIsingSquare_open_pathUses_west_iff_north n hn omega e
  have hES := fkIsingSquare_open_pathUses_east_iff_south n hn omega e
  by_cases hW : W
  · by_cases hE : E
    · exact Or.inr (Or.inr (Or.inl
        ⟨hW, hWN.1 hW, hE, hES.1 hE⟩))
    · exact Or.inl ⟨hW, hWN.1 hW, hE,
        fun hS => hE (hES.2 hS)⟩
  · by_cases hE : E
    · exact Or.inr (Or.inl ⟨hW,
        fun hN => hW (hWN.2 hN), hE, hES.1 hE⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hW,
        fun hN => hW (hWN.2 hN), hE,
        fun hS => hE (hES.2 hS)⟩))


theorem fkIsingSquare_double_visit_open_pair_exact
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) := by
  classical
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let G := fkIsingSquareLoopGraph n hn (setClosed e.1 omega)
  let p : G.Walk (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn (setClosed e.1 omega)
  have hp : p.IsPath :=
    (fkIsingSquareExplorationPath n hn (setClosed e.1 omega)).isPath
  have hWS := fkIsingSquare_closed_west_south_oriented_infix
    n hn omega e hwest
  have hEN := fkIsingSquare_closed_east_north_oriented_infix
    n hn omega e heast
  have hW : W ∈ p.support := by
    simpa [W, p, fkIsingSquarePathUsesLocalSide,
      fkIsingSquareExplorationOrder] using hwest
  have hS : S ∈ p.support := by
    simpa [S, p, fkIsingSquareExplorationOrder] using
      hWS.mem (by simp)
  have hE : E ∈ p.support := by
    simpa [E, p, fkIsingSquarePathUsesLocalSide,
      fkIsingSquareExplorationOrder] using heast
  have hN : N ∈ p.support := by
    simpa [N, p, fkIsingSquareExplorationOrder] using
      hEN.mem (by simp)
  have hiWS := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hWS
  have hiEN := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hEN
  change p.support.idxOf S = p.support.idxOf W + 1 at hiWS
  change p.support.idxOf N = p.support.idxOf E + 1 at hiEN
  have horder := fkIsingSquare_double_visit_closed_order
    n hn omega e hwest heast
  change p.support.idxOf S < p.support.idxOf E ∨
    p.support.idxOf N < p.support.idxOf W at horder
  have hopen : fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch G W S E N := by
    simpa [G, W, N, E, S] using
      fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  rcases horder with hSE | hNW
  · obtain ⟨q, hq, _hq_support, hWq, hNq, hSq, hEq⟩ :=
      walkSplice_membership_of_order G p hp hW hS hE hN
        (by omega) hSE (by omega)
    let qOpen : (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareMedialCarrier n) .terminal :=
      fkIsingSquareWalkCast hopen.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWalkCast_isPath] using hq
    have hmem (z : FKIsingSquareMedialCarrier n) :
        z ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) ↔
          z ∈ qOpen.support := by
      rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
        ← fkIsingSquarePath_mem_support_iff_reachable n hn
          (setOpen e.1 omega) qOpen hqOpen]
    have hWqOpen : W ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hWq
    have hNqOpen : N ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hNq
    have hSqOpen : S ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hSq
    have hEqOpen : E ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hEq
    left
    refine ⟨?_, ?_, ?_, ?_⟩
    · change W ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem W).2 hWqOpen
    · change N ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem N).2 hNqOpen
    · change E ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hEqOpen ((hmem E).1 h)
    · change S ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hSqOpen ((hmem S).1 h)
  · have hpair : medialTwoEdgeSwitch G E N W S =
        medialTwoEdgeSwitch G W S E N :=
      medialTwoEdgeSwitch_swap_pairs G W S E N
    have hopen' : fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
        medialTwoEdgeSwitch G E N W S := hopen.trans hpair.symm
    obtain ⟨q, hq, _hq_support, hEq, hSq, hNq, hWq⟩ :=
      walkSplice_membership_of_order G p hp hE hN hW hS
        (by omega) hNW (by omega)
    let qOpen : (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareMedialCarrier n) .terminal :=
      fkIsingSquareWalkCast hopen'.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWalkCast_isPath] using hq
    have hmem (z : FKIsingSquareMedialCarrier n) :
        z ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) ↔
          z ∈ qOpen.support := by
      rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
        ← fkIsingSquarePath_mem_support_iff_reachable n hn
          (setOpen e.1 omega) qOpen hqOpen]
    have hEqOpen : E ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hEq
    have hSqOpen : S ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hSq
    have hNqOpen : N ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hNq
    have hWqOpen : W ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hWq
    right
    refine ⟨?_, ?_, ?_, ?_⟩
    · change W ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hWqOpen ((hmem W).1 h)
    · change N ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hNqOpen ((hmem N).1 h)
    · change E ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem E).2 hEqOpen
    · change S ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem S).2 hSqOpen


theorem fkIsingSquare_local_switch_path_membership_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧
      ∀ side, ¬ fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e side) ∨
    (fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧
      ∀ side, fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e side) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧
      ∀ side, fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e side) ∨
    (fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east) := by
  simpa only [fkIsingSquarePathUsesLocalSide,
    mem_fkIsingSquareExplorationOrder_iff_finset] using
      fkIsingSquare_local_switch_component_classification n hn omega e


end
end StatMech.Universality
