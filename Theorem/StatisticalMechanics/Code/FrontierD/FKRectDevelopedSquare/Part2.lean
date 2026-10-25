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
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part2
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectSquareSiteVertex_developedSquareSite
    (R : FKRectTorus) (n : Nat) (z : Site 2) :
    fkRectSquareSiteVertex R (fkRectDevelopedSquareSite n z) =
      fkRectDevelopedSquareVertex R n z := by
  rfl

theorem fkRectDevelopedSquare_undevelop_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z)
    0 ≤ p.1 ∧ p.1 < R.width ∧ 0 ≤ p.2 ∧ p.2 < R.height := by
  rw [StatMech.RSW.Box.mem_rect] at hz
  dsimp [fkRectDevelopedSquarePoint, fkRectSquareUndevelopPoint]
  constructor
  · omega
  constructor
  · have hhalf :
        (z 0 - z 1 + (n : Int)) / 2 ≤ n := by omega
    omega
  constructor <;> omega


theorem fkRectVertexSquarePoint_developedSquareVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    fkRectVertexSquarePoint R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquarePoint n z := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedSquare_undevelop_bounds R n hwidth hheight hz
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

theorem fkRectVertexSquareSite_developedSquareVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    fkRectVertexSquareSite R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquareSite n z := by
  unfold fkRectVertexSquareSite fkRectDevelopedSquareSite
  rw [fkRectVertexSquarePoint_developedSquareVertex R n hwidth hheight hz]


theorem fkRectDevelopedSquareVertex_fst_succ_lt
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    (fkRectDevelopedSquareVertex R n z).1.val + 1 < R.width := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedSquare_undevelop_bounds R n hwidth hheight hz
  have hpoint := fkRectVertexSquarePoint_developedSquareVertex
    R n hwidth hheight hz
  have hundev := congrArg fkRectSquareUndevelopPoint hpoint
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at hundev
  have hx : ((fkRectDevelopedSquareVertex R n z).1.val : Int) = p.1 :=
    congrArg Prod.fst hundev
  rw [StatMech.RSW.Box.mem_rect] at hz
  have hpUpper : p.1 < 3 * (n : Int) := by
    dsimp [p, t, fkRectDevelopedSquarePoint,
      fkRectSquareUndevelopPoint]
    have hhalf :
        (z 0 - z 1 + (n : Int)) / 2 ≤ n := by omega
    omega
  exact_mod_cast (show
    ((fkRectDevelopedSquareVertex R n z).1.val : Int) + 1 < R.width by
      omega)


theorem fkRectDevelopedSquareVertex_injective_on
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height) :
    Set.InjOn (fkRectDevelopedSquareVertex R n)
      (StatMech.RSW.Box.rect 0 n 0 n) := by
  intro z hz w hw hzw
  have hs := congrArg (fkRectVertexSquarePoint R) hzw
  rw [fkRectVertexSquarePoint_developedSquareVertex R n hwidth hheight hz,
    fkRectVertexSquarePoint_developedSquareVertex R n hwidth hheight hw] at hs
  change (z 0 + 2 * (n : Int), z 1 + (n : Int)) =
    (w 0 + 2 * (n : Int), w 1 + (n : Int)) at hs
  have h0 := congrArg Prod.fst hs
  have h1 := congrArg Prod.snd hs
  apply funext
  intro i
  fin_cases i
  · exact add_right_cancel h0
  · exact add_right_cancel h1


theorem fkRectDevelopedSquareVertex_cutGraph_adj
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z w : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hw : w ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    (fkRectCutGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) := by
  rw [fkRectCutGraph_adj_iff_hypercubicAdj,
    fkRectVertexSquareSite_developedSquareVertex R n hwidth hheight hz,
    fkRectVertexSquareSite_developedSquareVertex R n hwidth hheight hw]
  rw [hypercubicLattice_adj] at hzw ⊢
  simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
    fkRectSquareSiteOfPair, Fin.sum_univ_two] using hzw


theorem fkRectLiftedDualEdge_sharedPrimalEdge
    (R : FKRectTorus) (e : R.EdgeIndex)
    (he : e ∉ fkRectTorusCutEdges R)
    (hd : fkRectEdgeToDualEdge R e ∉ fkRectTorusCutEdges R) :
    let d := fkRectEdgeToDualEdge R e
    let df := fkRectLiftedIndexedEdgeEnds R d
    let ep := fkRectLiftedIndexedEdgeEnds R e
    sharedPrimalEdge
        (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint df.1))
        (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint df.2)) =
      Sym2.map fkRectSquareSiteOfPair
        s(fkRectSquareDevelopPoint ep.1,
          fkRectSquareDevelopPoint ep.2) := by
  rcases e with ⟨b, x, y⟩
  cases b
  · have hx0 : x.val ≠ 0 := by
      intro hx
      apply he
      simp [mem_fkRectTorusCutEdges_iff, hx]
    have hy0 : y.val ≠ 0 := by
      intro hy
      apply he
      simp [mem_fkRectTorusCutEdges_iff, hy]
    have hxpred : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    have hxne : (x.val : Int) ≠ (x.val : Int) - 1 := by omega
    by_cases heven : Even y.val
    · obtain ⟨k, hk⟩ := heven
      have heven' : Even y.val := ⟨k, hk⟩
      have hyInt : (y.val : Int) = 2 * (k : Int) := by
        exact_mod_cast (show y.val = 2 * k by omega)
      have hdivSucc : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivPred : (2 * (k : Int) - 1) / 2 = k - 1 := by
        have : (0 : Int) < k := by omega
        omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven', hyInt, hxpred, hxne, hdivSucc, hdivPred] <;> omega
    · have hodd : Odd y.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hyInt : (y.val : Int) = 2 * (k : Int) + 1 := by exact_mod_cast hk
      have hdiv : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivSucc : (2 * (k : Int) + 1 + 1) / 2 = k + 1 := by omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven, hyInt, hxpred, hxne, hdiv, hdivSucc] <;> omega
  · have hy0 : y.val ≠ 0 := by
      intro hy
      apply he
      simp [mem_fkRectTorusCutEdges_iff, hy]
    have hx0 : x.val ≠ 0 := by
      intro hx
      apply hd
      simp [fkRectEdgeToDualEdge, mem_fkRectTorusCutEdges_iff, hx]
    have hxpred : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    have hxne : (x.val : Int) ≠ (x.val : Int) - 1 := by omega
    by_cases heven : Even y.val
    · obtain ⟨k, hk⟩ := heven
      have heven' : Even y.val := ⟨k, hk⟩
      have hyInt : (y.val : Int) = 2 * (k : Int) := by
        exact_mod_cast (show y.val = 2 * k by omega)
      have hdivSucc : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivPred : (2 * (k : Int) - 1) / 2 = k - 1 := by
        have : (0 : Int) < k := by omega
        omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven', hyInt, hxpred, hxne, hdivSucc, hdivPred] <;> omega
    · have hodd : Odd y.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hyInt : (y.val : Int) = 2 * (k : Int) + 1 := by exact_mod_cast hk
      have hdiv : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivSucc : (2 * (k : Int) + 1 + 1) / 2 = k + 1 := by omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven, hyInt, hxpred, hxne, hdiv, hdivSucc] <;> omega


theorem fkRectDualEdgeToEdge_not_cut_of_developedSquare
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {f g : Site 2} (hf : f ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hg : g ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (d : R.EdgeIndex)
    (hedge : fkRectTorusIndexedEdge R d =
      s(fkRectDevelopedSquareVertex R n f,
        fkRectDevelopedSquareVertex R n g))
    (hd : d ∉ fkRectTorusCutEdges R) :
    fkRectDualEdgeToEdge R d ∉ fkRectTorusCutEdges R := by
  rcases d with ⟨b, x, y⟩
  cases b
  · have hxy : y.val ≠ 0 ∧ x.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    simpa [fkRectDualEdgeToEdge,
      mem_fkRectTorusCutEdges_iff] using hxy.1
  · have hy0 : y.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    have hedge' := hedge
    simp only [fkRectTorusIndexedEdge, if_pos] at hedge'
    have hxface : x = (fkRectDevelopedSquareVertex R n f).1 ∨
        x = (fkRectDevelopedSquareVertex R n g).1 := by
      rcases Sym2.eq_iff.mp hedge' with h | h
      · exact Or.inl (congrArg Prod.fst h.1)
      · exact Or.inr (congrArg Prod.fst h.1)
    have hxsucc : x.val + 1 < R.width := by
      rcases hxface with hx | hx
      · rw [hx]
        exact fkRectDevelopedSquareVertex_fst_succ_lt R n hn
          hwidth hheight hf
      · rw [hx]
        exact fkRectDevelopedSquareVertex_fst_succ_lt R n hn
          hwidth hheight hg
    have hsucc : (finitePeriodicSucc R.width_pos x).val = x.val + 1 := by
      rw [finitePeriodicSucc_val]
      simp [ne_of_lt hxsucc]
    rw [mem_fkRectTorusCutEdges_iff]
    simp [fkRectDualEdgeToEdge, hy0, hsucc]


end
end StatMech.FrontierD
