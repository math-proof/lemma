/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part2
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectDevelopedThreeByOne_undevelop_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z)
    0 ≤ p.1 ∧ p.1 < R.width ∧ 0 ≤ p.2 ∧ p.2 < R.height := by
  change z ∈ rect 0 (3 * (n : Int)) 0 n at hz
  rw [mem_rect] at hz
  dsimp [fkRectDevelopedSquarePoint, fkRectSquareUndevelopPoint]
  have hhalfLower : 0 ≤ (z 0 - z 1 + (n : Int)) / 2 := by omega
  have hhalfUpper : (z 0 - z 1 + (n : Int)) / 2 ≤ 2 * n := by
    omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem fkRectVertexSquarePoint_developedThreeByOneVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    fkRectVertexSquarePoint R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquarePoint n z := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedThreeByOne_undevelop_bounds
    R n hwidth hheight hz
  change fkRectSquareDevelopPoint
      (((fkRectSquareRepresentativeVertex R t).1.val : Int),
        ((fkRectSquareRepresentativeVertex R t).2.val : Int)) = t
  have hx : ((fkRectSquareRepresentativeVertex R t).1.val : Int) = p.1 := by
    change ((p.1.natMod R.width : Nat) : Int) = p.1
    rw [Int.natMod, Int.emod_eq_of_lt hp.1 hp.2.1]
    exact Int.natCast_toNat_eq_self.mpr hp.1
  have hy : ((fkRectSquareRepresentativeVertex R t).2.val : Int) = p.2 := by
    change ((p.2.natMod R.height : Nat) : Int) = p.2
    rw [Int.natMod, Int.emod_eq_of_lt hp.2.2.1 hp.2.2.2]
    exact Int.natCast_toNat_eq_self.mpr hp.2.2.1
  rw [hx, hy]
  exact fkRectSquareDevelopPoint_undevelopPoint t

theorem fkRectVertexSquareSite_developedThreeByOneVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
    fkRectVertexSquareSite R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquareSite n z := by
  unfold fkRectVertexSquareSite fkRectDevelopedSquareSite
  rw [fkRectVertexSquarePoint_developedThreeByOneVertex
    R n hwidth hheight hz]

theorem fkRectDevelopedThreeByOneVertex_cutGraph_adj
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {z w : Site 2} (hz : z ∈ fkRectDevelopedThreeByOneRect n)
    (hw : w ∈ fkRectDevelopedThreeByOneRect n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    (fkRectCutGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) := by
  rw [fkRectCutGraph_adj_iff_hypercubicAdj,
    fkRectVertexSquareSite_developedThreeByOneVertex R n
      hwidth hheight hz,
    fkRectVertexSquareSite_developedThreeByOneVertex R n
      hwidth hheight hw]
  rw [hypercubicLattice_adj] at hzw ⊢
  simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
    fkRectSquareSiteOfPair, Fin.sum_univ_two] using hzw

theorem fkRectDevelopedThreeByOnePullback_open_iff
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) {z w : Site 2}
    (hz : z ∈ fkRectDevelopedThreeByOneRect n)
    (hw : w ∈ fkRectDevelopedThreeByOneRect n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    fkRectDevelopedSquarePullback R n omega s(z, w) = true ↔
      (fkRectOpenGraph R omega).Adj
        (fkRectDevelopedSquareVertex R n z)
        (fkRectDevelopedSquareVertex R n w) := by
  have hcut := fkRectDevelopedThreeByOneVertex_cutGraph_adj R n
    hwidth hheight hz hw hzw
  have htorus : (fkRectTorusGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) :=
    ((fkRectCutGraph_adj_iff R _ _).mp hcut).1
  rw [← fkOpenSub_fullGraphConfiguration]
  rw [StatMech.FK.openSub_adj]
  constructor
  · intro hopen
    refine ⟨htorus, ?_⟩
    simpa [fkRectDevelopedSquarePullback] using hopen
  · rintro ⟨_, hopen⟩
    simpa [fkRectDevelopedSquarePullback] using hopen

end
end StatMech.FrontierD
