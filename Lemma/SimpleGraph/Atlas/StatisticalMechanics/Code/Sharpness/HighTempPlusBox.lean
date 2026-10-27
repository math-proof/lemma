import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
open Finset SimpleGraph MeasureTheory StatMech StatMech.Sharpness


/--
[plusBoundaryField_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusBoundaryField_nonneg_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
-- given
  (x : {v // v ∈ Lambda}) :
-- imply
  0 ≤ plusBoundaryField Lambda x := by
-- proof
  apply StatMech.Sharpness.plusBoundaryField_nonneg Lambda x

/--
[gvBondTouch_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma gvBondTouch_endpoint_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {a b : Site d}
-- given
  (he : s(a, b) ∈ gvBondTouch Lambda) :
-- imply
  a ∈ Lambda ∨ b ∈ Lambda := by
-- proof
  apply StatMech.Sharpness.gvBondTouch_endpoint he

/--
[plusBoundary_edge_contribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusBoundary_edge_contribution_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {e : Sym2 (Site d)}
-- given
  (tau : ConfigSpace {v // v ∈ Lambda})
  (he : e ∈ plusBoundaryEdges Lambda) :
-- imply
  (∑ x : {v // v ∈ Lambda}, if x.1 ∈ e then spin tau x else 0) = bond (gvGlue (plusField d) Lambda tau) e := by
-- proof
  apply StatMech.Sharpness.plusBoundary_edge_contribution Lambda tau he

/--
[plusBoundary_bondSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusBoundary_bondSum_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
-- given
  (tau : ConfigSpace {v // v ∈ Lambda}) :
-- imply
  (∑ e ∈ plusBoundaryEdges Lambda, bond (gvGlue (plusField d) Lambda tau) e) = ∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x := by
-- proof
  apply StatMech.Sharpness.plusBoundary_bondSum Lambda tau

/--
[plusInternalEdges_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusInternalEdges_eq_map_eq
  {d : ℕ}
  {Lambda : Finset (Site d)} :
-- imply
  (gvBondTouch Lambda).filter (edgeInside Lambda) = (graphS d Lambda).edgeFinset.map (Function.Embedding.subtype (fun x : Site d ↦ x ∈ Lambda)).sym2Map := by
-- proof
  apply StatMech.Sharpness.plusInternalEdges_eq_map Lambda

/--
[plusInternal_bondSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusInternal_bondSum_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
-- given
  (tau : ConfigSpace {v // v ∈ Lambda}) :
-- imply
  (∑ e ∈ (gvBondTouch Lambda).filter (edgeInside Lambda), bond (gvGlue (plusField d) Lambda tau) e) = ∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e := by
-- proof
  apply StatMech.Sharpness.plusInternal_bondSum Lambda tau

/--
[plusTouch_bondSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusTouch_bondSum_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
-- given
  (tau : ConfigSpace {v // v ∈ Lambda}) :
-- imply
  (∑ e ∈ gvBondTouch Lambda, bond (gvGlue (plusField d) Lambda tau) e) = (∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e) + ∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x := by
-- proof
  apply StatMech.Sharpness.plusTouch_bondSum Lambda tau

/--
[unitEdgeCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma unitEdgeCoupling_nonneg_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {e : Sym2 V} :
-- imply
  0 ≤ unitEdgeCoupling G e := by
-- proof
  apply StatMech.Sharpness.unitEdgeCoupling_nonneg G e

/--
[unitEdgeCoupling_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma unitEdgeCoupling_edgeFinset_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  unitEdgeCoupling G e = 1 := by
-- proof
  apply StatMech.Sharpness.unitEdgeCoupling_edgeFinset G he

/--
[gvPlusWeight_eq_vertexFieldWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma gvPlusWeight_eq_vertexFieldWeight_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {beta : ℝ}
-- given
  (tau : ConfigSpace {v // v ∈ Lambda}) :
-- imply
  gvWeight (plusField d) Lambda beta 0 tau = vertexFieldWeight (graphS d Lambda) beta (unitEdgeCoupling (graphS d Lambda)) (plusBoundaryField Lambda) tau := by
-- proof
  apply StatMech.Sharpness.gvPlusWeight_eq_vertexFieldWeight Lambda beta tau

/--
[gvPlusZ_eq_vertexFieldZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma gvPlusZ_eq_vertexFieldZ_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {beta : ℝ} :
-- imply
  gvZ (plusField d) Lambda beta 0 = vertexFieldZ (graphS d Lambda) beta (unitEdgeCoupling (graphS d Lambda)) (plusBoundaryField Lambda) := by
-- proof
  apply StatMech.Sharpness.gvPlusZ_eq_vertexFieldZ Lambda beta

/--
[gvPlusProb_eq_vertexField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma gvPlusProb_eq_vertexField_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {beta : ℝ}
-- given
  (tau : ConfigSpace {v // v ∈ Lambda}) :
-- imply
  gvProb (plusField d) Lambda beta 0 tau = vertexFieldWeight (graphS d Lambda) beta (unitEdgeCoupling (graphS d Lambda)) (plusBoundaryField Lambda) tau / vertexFieldZ (graphS d Lambda) beta (unitEdgeCoupling (graphS d Lambda)) (plusBoundaryField Lambda) := by
-- proof
  apply StatMech.Sharpness.gvPlusProb_eq_vertexField Lambda beta tau

/--
[integral_gvMeasure_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma integral_gvMeasure_eq_sum_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {Lambda : Finset (Site d)}
  {f : ConfigSpace (Site d) → ℝ}
-- given
  (beta h : ℝ) :
-- imply
  ∫ omega, f omega ∂(gvMeasure eta Lambda beta h) = ∑ tau : ConfigSpace {v // v ∈ Lambda}, gvProb eta Lambda beta h tau * f (gvGlue eta Lambda tau) := by
-- proof
  apply StatMech.Sharpness.integral_gvMeasure_eq_sum eta Lambda beta h f

/--
[spinProd_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma spinProd_sourcePair_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {tau : ConfigSpace V}
  {a b : V} :
-- imply
  spinProd (sourcePair a b) tau = spin tau a * spin tau b := by
-- proof
  apply StatMech.Sharpness.spinProd_sourcePair tau a b

/--
[gvPlus_pair_eq_vertexField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma gvPlus_pair_eq_vertexField_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {beta : ℝ}
-- given
  (a b : {v // v ∈ Lambda}) :
-- imply
  (∫ omega, spin omega a.1 * spin omega b.1 ∂(gvPlusMeasure Lambda beta 0)) = vertexFieldTwoPoint (graphS d Lambda) beta (unitEdgeCoupling (graphS d Lambda)) (plusBoundaryField Lambda) a b := by
-- proof
  apply StatMech.Sharpness.gvPlus_pair_eq_vertexField Lambda beta a b

/--
[twoPointJ_congr_on_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma twoPointJ_congr_on_edges_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J K : Sym2 V → ℝ}
  {a b : V}
-- given
  (hJK : ∀ e ∈ G.edgeFinset, J e = K e) :
-- imply
  twoPointJ G beta J a b = twoPointJ G beta K a b := by
-- proof
  apply StatMech.Sharpness.twoPointJ_congr_on_edges G beta J K hJK a b

/--
[twoPointJ_couplingIn_unitEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma twoPointJ_couplingIn_unitEdge_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {beta : ℝ}
-- given
  (T : Finset {v // v ∈ Lambda})
  (a b : {v // v ∈ Lambda}) :
-- imply
  twoPointJ (graphS d Lambda) beta (couplingIn (unitEdgeCoupling (graphS d Lambda)) T) a b = twoPointJ (graphS d Lambda) beta (couplingIn (fun _ ↦ 1) T) a b := by
-- proof
  apply StatMech.Sharpness.twoPointJ_couplingIn_unitEdge Lambda beta T a b

/--
[mem_plusCutSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma mem_plusCutSites_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {T : Finset {v // v ∈ Lambda}}
  {x : {v // v ∈ Lambda}} :
-- imply
  x.1 ∈ plusCutSites T ↔ x ∈ T := by
-- proof
  apply StatMech.Sharpness.mem_plusCutSites

/--
[plusCutVertexEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusCutVertexEquiv_adj_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
-- given
  (T : Finset {v // v ∈ Lambda})
  (a b : {x : {v // v ∈ Lambda} // x ∈ T}) :
-- imply
  ((graphS d Lambda).comap (Subtype.val : {x : {v // v ∈ Lambda} // x ∈ T} → {v // v ∈ Lambda})).Adj a b ↔ (graphS d (plusCutSites T)).Adj (plusCutVertexEquiv T a) (plusCutVertexEquiv T b) := by
-- proof
  apply StatMech.Sharpness.plusCutVertexEquiv_adj T a b

/--
[corrOriginInner_origin_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma corrOriginInner_origin_of_mem_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Site d)}
-- given
  (ho : Percolation.origin d ∈ S) :
-- imply
  corrOriginInner d beta S (Percolation.origin d) = 1 := by
-- proof
  apply StatMech.Sharpness.corrOriginInner_origin_of_mem beta S ho

/--
[plus_localCorr_eq_corrOriginInner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plus_localCorr_eq_corrOriginInner_eq
  {d : ℕ}
  {Lambda : Finset (Site d)}
  {beta : ℝ}
  {o x : {v // v ∈ Lambda}}
-- given
  (T : Finset {v // v ∈ Lambda})
  (ho : o ∈ T)
  (hx : x ∈ T)
  (horigin : o.1 = Percolation.origin d) :
-- imply
  twoPointJ (graphS d Lambda) beta (couplingIn (unitEdgeCoupling (graphS d Lambda)) T) o x = corrOriginInner d beta (plusCutSites T) x.1 := by
-- proof
  apply StatMech.Sharpness.plus_localCorr_eq_corrOriginInner Lambda beta T ho hx horigin

/--
[mem_sitesInVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma mem_sitesInVolume_eq
  {d : ℕ}
  {Lambda T : Finset (Site d)}
  {x : {v // v ∈ Lambda}} :
-- imply
  x ∈ sitesInVolume Lambda T ↔ x.1 ∈ T := by
-- proof
  apply StatMech.Sharpness.mem_sitesInVolume

/--
[plusBoundaryField_eq_zero_of_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusBoundaryField_eq_zero_of_neighbors_eq
  {d : ℕ}
  {Lambda T : Finset (Site d)}
-- given
  (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
  (x : {v // v ∈ Lambda})
  (hx : x ∈ sitesInVolume Lambda T) :
-- imply
  plusBoundaryField Lambda x = 0 := by
-- proof
  apply StatMech.Sharpness.plusBoundaryField_eq_zero_of_neighbors Lambda T hnbr x hx

/--
[gvPlus_simon_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma gvPlus_simon_subtype_eq
  {d : ℕ}
  {Lambda T : Finset (Site d)}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
  (o z : {v // v ∈ Lambda})
  (ho : o.1 ∈ T)
  (hz : z.1 ∉ T) :
-- imply
  (∫ omega, spin omega o.1 * spin omega z.1 ∂(gvPlusMeasure Lambda beta 0)) ≤ ∑ x ∈ sitesInVolume Lambda T, ∑ y ∈ (Finset.univ \ sitesInVolume Lambda T), Real.tanh (beta * unitEdgeCoupling (graphS d Lambda) s(x, y)) * twoPointJ (graphS d Lambda) beta (couplingIn (unitEdgeCoupling (graphS d Lambda)) (sitesInVolume Lambda T)) o x * (∫ omega, spin omega y.1 * spin omega z.1 ∂(gvPlusMeasure Lambda beta 0)) := by
-- proof
  apply StatMech.Sharpness.gvPlus_simon_subtype Lambda T beta hbeta hnbr o z ho hz

/--
[plusCutSites_sitesInVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusCutSites_sitesInVolume_eq
  {d : ℕ}
  {Lambda T : Finset (Site d)}
-- given
  (hsub : T ⊆ Lambda) :
-- imply
  plusCutSites (sitesInVolume Lambda T) = T := by
-- proof
  apply StatMech.Sharpness.plusCutSites_sitesInVolume Lambda T hsub

/--
[gvPlus_simon_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma gvPlus_simon_ambient_eq
  {d : ℕ}
  {Lambda T : Finset (Site d)}
  {beta : ℝ}
  {z : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hsub : T ⊆ Lambda)
  (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
  (ho : Percolation.origin d ∈ T)
  (hzL : z ∈ Lambda)
  (hzT : z ∉ T) :
-- imply
  (∫ omega, spin omega (Percolation.origin d) * spin omega z ∂(gvPlusMeasure Lambda beta 0)) ≤ simonBoundaryIntegral beta T (Percolation.origin d) z (gvPlusMeasure Lambda beta 0) := by
-- proof
  apply StatMech.Sharpness.gvPlus_simon_ambient Lambda T beta hbeta hsub hnbr ho z hzL hzT

/--
[plusMeasure_simon_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusMeasure_simon_box_eq
  {d : ℕ}
  {n : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
  {z : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hsub : T ⊆ boxFinset d n)
  (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ boxFinset d n)
  (ho : Percolation.origin d ∈ T)
  (hzL : z ∈ boxFinset d n)
  (hzT : z ∉ T) :
-- imply
  (∫ omega, spin omega (Percolation.origin d) * spin omega z ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) ≤ simonBoundaryIntegral beta T (Percolation.origin d) z (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Sharpness.plusMeasure_simon_box n beta hbeta T hsub hnbr ho z hzL hzT

/--
[plusMeasure_simon_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusMeasure_simon_eventually_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
  {z : Site d}
  {phi : ℕ → ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (ho : Percolation.origin d ∈ T)
  (hzT : z ∉ T)
  (hphi : StrictMono phi) :
-- imply
  ∀ᶠ n in Filter.atTop, (∫ omega, spin omega (Percolation.origin d) * spin omega z ∂(plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d)))) ≤ simonBoundaryIntegral beta T (Percolation.origin d) z (plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Sharpness.plusMeasure_simon_eventually beta hbeta T ho z hzT phi hphi

/--
[plusCorr_simon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean)
-/
@[path]
private lemma plusCorr_simon_eq
  {d : ℕ}
  {beta : ℝ}
  {T : Finset (Site d)}
  {z : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (ho : Percolation.origin d ∈ T)
  (hzT : z ∉ T) :
-- imply
  plusCorr d beta (Percolation.origin d) z ≤ simonBoundaryPlus beta T (Percolation.origin d) z := by
-- proof
  apply StatMech.Sharpness.plusCorr_simon beta hbeta T ho z hzT


-- created on 2026-10-23
