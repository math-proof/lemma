import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing
open Finset StatMech StatMech.FrontierA


/--
[gaugeSurfaceBoundary_union_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma gaugeSurfaceBoundary_union_of_disjoint_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {A B : Finset P}
-- given
  (hAB : Disjoint A B) :
-- imply
  gaugeSurfaceBoundary incidence (A ∪ B) = gaugeSurfaceBoundary incidence A ∆ gaugeSurfaceBoundary incidence B := by
-- proof
  apply StatMech.FrontierA.gaugeSurfaceBoundary_union_of_disjoint incidence hAB

/--
[plaquetteIncidenceCount_map_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma plaquetteIncidenceCount_map_apply_eq
  [Fintype E]
  [DecidableEq E]
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {A : Finset Psmall}
  {e : Esmall}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb) :
-- imply
  plaquetteIncidenceCount incidenceBig (A.map pEmb) (eEmb e) = plaquetteIncidenceCount incidenceSmall A e := by
-- proof
  apply StatMech.FrontierA.plaquetteIncidenceCount_map_apply incidenceSmall incidenceBig eEmb pEmb hinc A e

/--
[plaquetteIncidenceCount_map_apply_of_not_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma plaquetteIncidenceCount_map_apply_of_not_mem_range_eq
  [Fintype E]
  [DecidableEq E]
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {A : Finset Psmall}
  {e : Ebig}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
  (he : e ∉ Set.range eEmb) :
-- imply
  plaquetteIncidenceCount incidenceBig (A.map pEmb) e = 0 := by
-- proof
  apply StatMech.FrontierA.plaquetteIncidenceCount_map_apply_of_not_mem_range incidenceSmall incidenceBig eEmb pEmb hinc A he

/--
[gaugeSurfaceBoundary_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma gaugeSurfaceBoundary_map_eq
  [Fintype E]
  [DecidableEq E]
  {incidenceSmall : Psmall → Finset Esmall}
  {incidenceBig : Pbig → Finset Ebig}
  {eEmb : Esmall ↪ Ebig}
  {pEmb : Psmall ↪ Pbig}
  {A : Finset Psmall}
-- given
  (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb) :
-- imply
  gaugeSurfaceBoundary incidenceBig (A.map pEmb) = (gaugeSurfaceBoundary incidenceSmall A).map eEmb := by
-- proof
  apply StatMech.FrontierA.gaugeSurfaceBoundary_map incidenceSmall incidenceBig eEmb pEmb hinc A

/--
[finOffsetEmbedding_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma finOffsetEmbedding_val_eq
  [Fintype E]
  [DecidableEq E]
  {n N : Nat}
  {offset : Nat}
  {i : Fin n}
-- given
  (h : offset + n ≤ N) :
-- imply
  (finOffsetEmbedding offset h i).val = offset + i.val := by
-- proof
  apply StatMech.FrontierA.finOffsetEmbedding_val offset h i

/--
[finOffsetEmbedding_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma finOffsetEmbedding_castSucc_eq
  [Fintype E]
  [DecidableEq E]
  {n N : Nat}
  {offset : Nat}
  {i : Fin n}
-- given
  (h : offset + n ≤ N) :
-- imply
  finOffsetEmbedding offset (by omega : offset + (n + 1) ≤ N + 1) i.castSucc = (finOffsetEmbedding offset h i).castSucc := by
-- proof
  apply StatMech.FrontierA.finOffsetEmbedding_castSucc offset h i

/--
[finOffsetEmbedding_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma finOffsetEmbedding_succ_eq
  [Fintype E]
  [DecidableEq E]
  {n N : Nat}
  {offset : Nat}
  {i : Fin n}
-- given
  (h : offset + n ≤ N) :
-- imply
  finOffsetEmbedding offset (by omega : offset + (n + 1) ≤ N + 1) i.succ = (finOffsetEmbedding offset h i).succ := by
-- proof
  apply StatMech.FrontierA.finOffsetEmbedding_succ offset h i

/--
[finOffsetEmbedding_castSucc'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma finOffsetEmbedding_castSucc'_eq
  [Fintype E]
  [DecidableEq E]
  {n N : Nat}
  {offset : Nat}
  {i : Fin n}
-- given
  (h : offset + (n + 1) ≤ N + 1) :
-- imply
  finOffsetEmbedding offset h i.castSucc = (finOffsetEmbedding offset (by omega) i).castSucc := by
-- proof
  apply StatMech.FrontierA.finOffsetEmbedding_castSucc' offset h i

/--
[finOffsetEmbedding_succ'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma finOffsetEmbedding_succ'_eq
  [Fintype E]
  [DecidableEq E]
  {n N : Nat}
  {offset : Nat}
  {i : Fin n}
-- given
  (h : offset + (n + 1) ≤ N + 1) :
-- imply
  finOffsetEmbedding offset h i.succ = (finOffsetEmbedding offset (by omega) i).succ := by
-- proof
  apply StatMech.FrontierA.finOffsetEmbedding_succ' offset h i

/--
[cubicalPlaquetteIncidence_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalPlaquetteIncidence_chart_eq
  [Fintype E]
  [DecidableEq E]
  {a b c A B C : Nat}
  {ox oy oz : Nat}
  {p : CubicalPlaquette a b c}
-- given
  (hx : ox + a ≤ A)
  (hy : oy + b ≤ B)
  (hz : oz + c ≤ C) :
-- imply
  cubicalPlaquetteIncidence (cubicalPlaquetteChart ox oy oz hx hy hz p) = (cubicalPlaquetteIncidence p).map (cubicalEdgeChart ox oy oz hx hy hz) := by
-- proof
  apply StatMech.FrontierA.cubicalPlaquetteIncidence_chart ox oy oz hx hy hz p

/--
[cubicalXYWilsonExpectation_le_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_le_chart_eq
  [Fintype E]
  [DecidableEq E]
  {a b c A B C : Nat}
  {ox oy oz : Nat}
  {beta : Real}
  {z : Fin (c + 1)}
-- given
  (hx : ox + a ≤ A)
  (hy : oy + b ≤ B)
  (hz : oz + c ≤ C)
  (hbeta : 0 ≤ beta) :
-- imply
  gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette a b c => beta) (cubicalXYLoop z) ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette A B C => beta) ((cubicalXYLoop z).map (cubicalEdgeChart ox oy oz hx hy hz)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_le_chart ox oy oz hx hy hz hbeta z

/--
[cubicalXYSheet_horizontal_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalXYSheet_horizontal_union_eq
  [Fintype E]
  [DecidableEq E]
  {m l n c₁ c₂ C : Nat}
-- given
  (hc₁ : c₁ ≤ C)
  (hc₂ : c₂ ≤ C) :
-- imply
  (cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map (cubicalPlaquetteChart 0 0 0 (by omega) (by omega) (by omega)) ∪ (cubicalXYSheet (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map (cubicalPlaquetteChart m 0 0 (by omega) (by omega) (by omega)) = cubicalXYSheet (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheet_horizontal_union m l n c₁ c₂ C hc₁ hc₂

/--
[cubicalXYSheet_horizontal_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalXYSheet_horizontal_disjoint_eq
  [Fintype E]
  [DecidableEq E]
  {m l n c₁ c₂ C : Nat}
-- given
  (hc₁ : c₁ ≤ C)
  (hc₂ : c₂ ≤ C) :
-- imply
  Disjoint ((cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map (cubicalPlaquetteChart (A := m + l) (B := n) (C := C) 0 0 0 (by omega) (by omega) (by omega))) ((cubicalXYSheet (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map (cubicalPlaquetteChart (A := m + l) (B := n) (C := C) m 0 0 (by omega) (by omega) (by omega))) := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheet_horizontal_disjoint m l n c₁ c₂ C hc₁ hc₂

/--
[cubicalXYLoop_horizontal_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalXYLoop_horizontal_symmDiff_eq
  [Fintype E]
  [DecidableEq E]
  {m l n c₁ c₂ C : Nat}
-- given
  (hc₁ : c₁ ≤ C)
  (hc₂ : c₂ ≤ C) :
-- imply
  (cubicalXYLoop (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map (cubicalEdgeChart (A := m + l) (B := n) (C := C) 0 0 0 (by omega) (by omega) (by omega)) ∆ (cubicalXYLoop (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map (cubicalEdgeChart (A := m + l) (B := n) (C := C) m 0 0 (by omega) (by omega) (by omega)) = cubicalXYLoop (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYLoop_horizontal_symmDiff m l n c₁ c₂ C hc₁ hc₂

/--
[cubicalXYSheet_vertical_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalXYSheet_vertical_union_eq
  [Fintype E]
  [DecidableEq E]
  {m n k c₁ c₂ C : Nat}
-- given
  (hc₁ : c₁ ≤ C)
  (hc₂ : c₂ ≤ C) :
-- imply
  (cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map (cubicalPlaquetteChart 0 0 0 (by omega) (by omega) (by omega)) ∪ (cubicalXYSheet (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map (cubicalPlaquetteChart 0 n 0 (by omega) (by omega) (by omega)) = cubicalXYSheet (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheet_vertical_union m n k c₁ c₂ C hc₁ hc₂

/--
[cubicalXYSheet_vertical_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalXYSheet_vertical_disjoint_eq
  [Fintype E]
  [DecidableEq E]
  {m n k c₁ c₂ C : Nat}
-- given
  (hc₁ : c₁ ≤ C)
  (hc₂ : c₂ ≤ C) :
-- imply
  Disjoint ((cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map (cubicalPlaquetteChart (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega))) ((cubicalXYSheet (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map (cubicalPlaquetteChart (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega))) := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheet_vertical_disjoint m n k c₁ c₂ C hc₁ hc₂

/--
[cubicalXYLoop_vertical_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalXYLoop_vertical_symmDiff_eq
  [Fintype E]
  [DecidableEq E]
  {m n k c₁ c₂ C : Nat}
-- given
  (hc₁ : c₁ ≤ C)
  (hc₂ : c₂ ≤ C) :
-- imply
  (cubicalXYLoop (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map (cubicalEdgeChart (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega)) ∆ (cubicalXYLoop (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map (cubicalEdgeChart (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega)) = cubicalXYLoop (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYLoop_vertical_symmDiff m n k c₁ c₂ C hc₁ hc₂

/--
[cubicalRectangularWilsonExpectation_mul_le_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonExpectation_mul_le_horizontal_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {m l n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalRectangularWilsonExpectation beta m n * cubicalRectangularWilsonExpectation beta l n ≤ cubicalRectangularWilsonExpectation beta (m + l) n := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonExpectation_mul_le_horizontal hbeta m l n

/--
[cubicalRectangularWilsonExpectation_mul_le_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonExpectation_mul_le_vertical_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {m n k : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  cubicalRectangularWilsonExpectation beta m n * cubicalRectangularWilsonExpectation beta m k ≤ cubicalRectangularWilsonExpectation beta m (n + k) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonExpectation_mul_le_vertical hbeta m n k

/--
[gaugeWilsonExpectation_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_empty_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype E]
  [DecidableEq E]
  [Fintype P]
  [DecidableEq P]
  {incidence : P → Finset E}
  {K : P → Real} :
-- imply
  gaugeWilsonExpectation incidence K ∅ = 1 := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_empty incidence K

/--
[cubicalRectangularWilsonExpectation_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonExpectation_zero_left_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {n : Nat} :
-- imply
  cubicalRectangularWilsonExpectation beta 0 n = 1 := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonExpectation_zero_left beta n

/--
[cubicalRectangularWilsonExpectation_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonExpectation_zero_right_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {m : Nat} :
-- imply
  cubicalRectangularWilsonExpectation beta m 0 = 1 := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonExpectation_zero_right beta m

/--
[cubicalRectangularWilsonExpectation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonExpectation_pos_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {m n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 < cubicalRectangularWilsonExpectation beta m n := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonExpectation_pos hbeta m n

/--
[cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {m n : Nat} :
-- imply
  cubicalRectangularWilsonFreeEnergy beta m n = -Real.log (cubicalRectangularWilsonExpectation beta m n) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation beta m n

/--
[cubicalRectangularWilsonFreeEnergy_horizontal_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_horizontal_subadditive_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  HorizontallySubadditive (cubicalRectangularWilsonFreeEnergy beta) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_horizontal_subadditive hbeta

/--
[cubicalRectangularWilsonFreeEnergy_vertical_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_vertical_subadditive_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  VerticallySubadditive (cubicalRectangularWilsonFreeEnergy beta) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_vertical_subadditive hbeta

/--
[cubicalRectangularWilsonFreeEnergy_separatelySubadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_separatelySubadditive_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  SeparatelySubadditive (cubicalRectangularWilsonFreeEnergy beta) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_separatelySubadditive hbeta

/--
[cubicalRectangularWilsonFreeEnergy_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_zero_left_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {n : Nat} :
-- imply
  cubicalRectangularWilsonFreeEnergy beta 0 n = 0 := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_zero_left beta n

/--
[cubicalRectangularWilsonFreeEnergy_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_zero_right_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
  {m : Nat} :
-- imply
  cubicalRectangularWilsonFreeEnergy beta m 0 = 0 := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_zero_right beta m

/--
[cubicalRectangularWilsonFreeEnergy_hasAreaBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_hasAreaBound_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  HasRectangularAreaBound (cubicalRectangularWilsonFreeEnergy beta) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_hasAreaBound hbeta

/--
[cubicalRectangularWilsonFreeEnergy_hasBlockGluing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_hasBlockGluing_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  HasRectangularBlockGluing (cubicalRectangularWilsonFreeEnergy beta) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_hasBlockGluing hbeta

/--
[cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate_unconditional_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (cubicalSquareWilsonDensity beta) Filter.atTop (nhds (rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta))) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate_unconditional hbeta

/--
[cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean)
-/
@[path]
private lemma cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate_unconditional_eq
  [Fintype E]
  [DecidableEq E]
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (cubicalSquareDisorderDensity beta) Filter.atTop (nhds (rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta))) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate_unconditional hbeta


-- created on 2026-10-23
