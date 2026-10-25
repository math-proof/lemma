/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part5
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredPred_mem
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hx : fkIsingSquareWiredArc n x)
    (hgt : -(n : Int) < x.1 1) :
    fkIsingSquareWiredArc n (fkIsingSquareWiredPred n x hx hgt) := rfl

theorem fkIsingSquareWiredPred_adj
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hx : fkIsingSquareWiredArc n x)
    (hgt : -(n : Int) < x.1 1) :
    (fkIsingSquareWiredArcPathGraph n).Adj
      (fkIsingSquareWiredPred n x hx hgt) x := by
  refine ⟨?_, rfl, hx⟩
  change (hypercubicLattice 2).Adj
    (![-(n : Int), x.1 1 - 1] : Site 2) x.1
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  have hx0 : x.1 0 = -(n : Int) := hx
  simp [hx0]


theorem fkIsingSquareWiredArcPath_reachable_markedA
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hx : fkIsingSquareWiredArc n x) :
    (fkIsingSquareWiredArcPathGraph n).Reachable
      (fkIsingSquareMarkedA n) x := by
  let height : (fkSquareBoxPlanar n).V → Nat :=
    fun z => (z.1 1 + (n : Int)).natAbs
  induction hk : height x using Nat.strong_induction_on generalizing x with
  | h k ih =>
      by_cases hbase : x = fkIsingSquareMarkedA n
      · subst x
        exact Reachable.refl _
      have hb := fkIsingSquareVertex_coordinate_bounds n x 1
      have hgt : -(n : Int) < x.1 1 := by
        have hne : x.1 1 ≠ -(n : Int) := by
          intro hy
          apply hbase
          apply Subtype.ext
          funext i
          fin_cases i
          · simpa [fkIsingSquareMarkedA] using hx
          · simpa [fkIsingSquareMarkedA] using hy
        omega
      let z := fkIsingSquareWiredPred n x hx hgt
      have hz : fkIsingSquareWiredArc n z := by
        exact fkIsingSquareWiredPred_mem n x hx hgt
      have hxnonneg : 0 ≤ x.1 1 + (n : Int) := by omega
      have hzcoord : z.1 1 = x.1 1 - 1 := rfl
      have hznonneg : 0 ≤ z.1 1 + (n : Int) := by
        rw [hzcoord]
        omega
      have hheight : height z < height x := by
        have heq : z.1 1 + (n : Int) + 1 = x.1 1 + (n : Int) := by
          rw [hzcoord]
          ring
        have habs : (z.1 1 + (n : Int)).natAbs + 1 =
            (x.1 1 + (n : Int)).natAbs := by
          have hcast :
              (((z.1 1 + (n : Int)).natAbs + 1 : Nat) : Int) =
                (((x.1 1 + (n : Int)).natAbs : Nat) : Int) := by
            push_cast
            rw [abs_of_nonneg hznonneg, abs_of_nonneg hxnonneg]
            exact heq
          exact_mod_cast hcast
        change (z.1 1 + (n : Int)).natAbs <
          (x.1 1 + (n : Int)).natAbs
        omega
      have hheightK : height z < k := by
        rw [← hk]
        exact hheight
      have hAz := ih (height z) hheightK z hz rfl
      exact hAz.trans (fkIsingSquareWiredPred_adj n x hx hgt).reachable


theorem fkIsingSquareWiredArcPath_reachable
    (n : Nat) {x y : (fkSquareBoxPlanar n).V}
    (hx : fkIsingSquareWiredArc n x)
    (hy : fkIsingSquareWiredArc n y) :
    (fkIsingSquareWiredArcPathGraph n).Reachable x y :=
  (fkIsingSquareWiredArcPath_reachable_markedA n x hx).symm.trans
    (fkIsingSquareWiredArcPath_reachable_markedA n y hy)

theorem reachable_of_step_reachable
    {V : Type*} {G K : SimpleGraph V}
    (hstep : ∀ {x y}, G.Adj x y → K.Reachable x y)
    {x y : V} (hxy : G.Reachable x y) : K.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons huv p ih => exact (hstep huv).trans ih


theorem fkIsingSquare_sup_wiredArcPath_reachable_iff_clique
    (n : Nat) (H : SimpleGraph (fkSquareBoxPlanar n).V)
    (x y : (fkSquareBoxPlanar n).V) :
    (H ⊔ fkIsingSquareWiredArcPathGraph n).Reachable x y ↔
      (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
  classical
  constructor
  · exact Reachable.mono (sup_le_sup_left
      (fkIsingSquareWiredArcPathGraph_le_clique n) H)
  · intro hxy
    apply reachable_of_step_reachable (G :=
      H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)) (K :=
      H ⊔ fkIsingSquareWiredArcPathGraph n) ?_ hxy
    intro u v huv
    rcases huv with hH | hclique
    · exact (show (H ⊔ fkIsingSquareWiredArcPathGraph n).Adj u v from
        Or.inl hH).reachable
    · rw [boundaryCliqueGraph_adj] at hclique
      exact (fkIsingSquareWiredArcPath_reachable n
        hclique.2.1 hclique.2.2).mono le_sup_right


theorem fkIsingSquare_openSub_wireConfig
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    openSub (fkSquareBoxPlanar n).G (fkIsingSquareWireConfig n omega) =
      openSub (fkSquareBoxPlanar n).G omega ⊔
        fkIsingSquareWiredArcPathGraph n := by
  ext x y
  simp only [openSub_adj, sup_adj, fkIsingSquareWiredArcPathGraph]
  constructor
  · rintro ⟨hxy, hopen⟩
    by_cases hw : fkIsingSquareIsWiredArcEdge n s(x, y)
    · right
      exact ⟨hxy, hw x (by simp), hw y (by simp)⟩
    · left
      exact ⟨hxy, by simpa [fkIsingSquareWireConfig, hw] using hopen⟩
  · rintro (⟨hxy, hopen⟩ | ⟨hxy, hx, hy⟩)
    · exact ⟨hxy, by
        by_cases hw : fkIsingSquareIsWiredArcEdge n s(x, y)
        · simp [fkIsingSquareWireConfig, hw]
        · simpa [fkIsingSquareWireConfig, hw] using hopen⟩
    · exact ⟨hxy, fkIsingSquareWireConfig_wired n omega (by
        intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy)⟩


theorem fkIsingSquare_wireConfig_reachable_iff_gadget
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : (fkSquareBoxPlanar n).V) :
    (openSub (fkSquareBoxPlanar n).G
        (fkIsingSquareWireConfig n omega)).Reachable x y ↔
      (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G omega) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
          (.physical x) (.physical y) := by
  rw [fkIsingSquare_openSub_wireConfig,
    fkIsingSquare_sup_wiredArcPath_reachable_iff_clique,
    fkIsingSquare_openWiredExteriorGadget_reachable_iff]


end
end StatMech.Universality
