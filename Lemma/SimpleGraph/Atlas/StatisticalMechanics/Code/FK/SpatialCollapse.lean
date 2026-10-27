import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.SpatialCollapse
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[spc_growingBox_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_growingBox_collapse_eq
  {d : ℕ}
  {t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.spc_growingBox_collapse t hE L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[spc_boundaryFraction_le_surfaceVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_boundaryFraction_le_surfaceVolume_eq
  {d : ℕ}
  {n : ℕ}
  {C : ℝ}
  {In : Finset (Sym2 (boxVerts d n))}
-- given
  (hC : 0 ≤ C)
  (hIE : In ⊆ (boxGraph d n).edgeFinset)
  (hbd : ((boxGraph d n).edgeFinset.card - In.card : ℝ) ≤ C * (Finset.univ.filter (boxBoundary d n)).card)
  (hEpos : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  (((boxGraph d n).edgeFinset.card - In.card : ℝ)) / (boxGraph d n).edgeFinset.card ≤ C * (((Finset.univ.filter (boxBoundary d n)).card : ℝ) / (boxGraph d n).edgeFinset.card) := by
-- proof
  apply StatMech.FK.spc_boundaryFraction_le_surfaceVolume n C hC In hIE hbd hEpos

/--
[spc_growingBox_collapse_of_uniformBulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_growingBox_collapse_of_uniformBulk_eq
  {d : ℕ}
  {t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {C : ℝ}
  {δ : ℕ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hC : 0 ≤ C)
  (hbd : ∀ n, ((boxGraph d n).edgeFinset.card - (In n).card : ℝ) ≤ C * (Finset.univ.filter (boxBoundary d n)).card)
  (hbd0 : ∀ n, 0 ≤ ((boxGraph d n).edgeFinset.card - (In n).card : ℝ))
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n) :
-- imply
  Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.spc_growingBox_collapse_of_uniformBulk hd t hE L hL0 hL1 In hIE C hC hbd hbd0 δ hδ0 hδlim hin

/--
[spc_offCentreCarrier_gives_homogeneity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_offCentreCarrier_gives_homogeneity_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcarrier : Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0))
  (htrans : ∀ k, edgeMargProb (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')) = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.spc_offCentreCarrier_gives_homogeneity N v eb eb' hp hp1 hcarrier htrans

/--
[spc_uniformBulk_is_offCentreCarrier_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_uniformBulk_is_offCentreCarrier_remark_eq
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.spc_uniformBulk_is_offCentreCarrier_remark

/--
[spc_tiltFreeEnergy_instIrrel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_tiltFreeEnergy_instIrrel_eq
  {d : ℕ}
  {N : ℕ}
  {H : SimpleGraph (boxVerts d N)}
  {i1 i2 : DecidableRel H.Adj}
  {t : ℝ} :
-- imply
  @ivp2_tiltFreeEnergy _ _ _ H i1 2 t = @ivp2_tiltFreeEnergy _ _ _ H i2 2 t := by
-- proof
  apply StatMech.FK.spc_tiltFreeEnergy_instIrrel N H i1 i2 t

/--
[spc_range_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_range_finite_eq
  {d : ℕ}
  {N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [inst : ∀ n, DecidableRel (Gn n).Adj]
  {t : ℝ} :
-- imply
  (Set.range (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t)).Finite := by
-- proof
  apply StatMech.FK.spc_range_finite N Gn t

/--
[spc_feketeLimit_mem_finiteRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_feketeLimit_mem_finiteRange_eq
  {d : ℕ}
  {N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t))) :
-- imply
  g t ∈ Set.range (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) := by
-- proof
  apply StatMech.FK.spc_feketeLimit_mem_finiteRange N Gn g hfree t

/--
[spc_fixedBox_collapse_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_fixedBox_collapse_obstruction_eq
  {d : ℕ}
  {N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t))) :
-- imply
  (∃ H : SimpleGraph (boxVerts d N), ∃ _ : DecidableRel H.Adj, g t = ivp2_tiltFreeEnergy H 2 t) ∧ Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)) := by
-- proof
  apply StatMech.FK.spc_fixedBox_collapse_obstruction N Gn g hfree hboxfree t

/--
[spc_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SpatialCollapse.lean)
-/
@[path]
private lemma spc_residue_remark_eq
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.spc_residue_remark


-- created on 2026-10-23
