import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.PcUpperViaFK
open MeasureTheory Filter Topology Set Finset StatMech StatMech.FK StatMech.Percolation


/--
[bernoulliProduct_map_injective_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma bernoulliProduct_map_injective_restrict_eq
  [Countable I]
  [Countable E]
  {f : I → E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hf : Function.Injective f) :
-- imply
  Measure.map (fun (omega : ConfigSpace E) (i : I) => omega (f i)) (bernoulliProductMeasure (E := E) p hp) = bernoulliProductMeasure (E := I) p hp := by
-- proof
  apply StatMech.FK.bernoulliProduct_map_injective_restrict p hp f hf

/--
[fkProbOne_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma fkProbOne_pattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {eta : ConfigSpace ↥G.edgeFinset} :
-- imply
  ∑ omega : ConfigSpace (Sym2 V), (if G.edgeFinset.restrict omega = eta then (1 : ℝ) else 0) * fkProb G p 1 omega = configWeight p eta := by
-- proof
  apply StatMech.FK.fkProbOne_pattern G p eta

/--
[fkProbOne_event_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma fkProbOne_event_eq_bernoulli_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) (G.edgeFinset : Set (Sym2 V))) :
-- imply
  ∑ omega : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) omega * fkProb G p 1 omega = (bernoulliProductMeasure (E := Sym2 V) ⟨p, hp.le⟩ (by exact_mod_cast hp1.le)).real A := by
-- proof
  apply StatMech.FK.fkProbOne_event_eq_bernoulli G hp hp1 A hA

/--
[connToBdryEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma connToBdryEvent_dependsOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  _root_.DependsOn ({omega : ConfigSpace (Sym2 V) | IsingFK.ConnToBdry G bdry omega x}.indicator (fun _ => (1 : ℝ))) (G.edgeFinset : Set (Sym2 V)) := by
-- proof
  apply StatMech.FK.connToBdryEvent_dependsOn G G bdry x

/--
[bernoulliProduct_map_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma bernoulliProduct_map_boxRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map (boxRestrict d n) (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) = bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp := by
-- proof
  apply StatMech.FK.bernoulliProduct_map_boxRestrict G p hp n

/--
[bernoulliProduct_boxRestrict_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma bernoulliProduct_boxRestrict_preimage_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {n : ℕ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (boxRestrict d n ⁻¹' A) = (bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp).real A := by
-- proof
  apply StatMech.FK.bernoulliProduct_boxRestrict_preimage G p hp n A

/--
[wiredFinite_boxBdryConnEvent_le_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma wiredFinite_boxBdryConnEvent_le_bernoulli_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d n (by exact_mod_cast hp0) (by exact_mod_cast hp1) (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1.le).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.wiredFinite_boxBdryConnEvent_le_bernoulli G p hp0 hp1 n

/--
[fkTheta_two_le_bernoulliTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma fkTheta_two_le_bernoulliTheta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  fkTheta d (by exact_mod_cast hp0) (by exact_mod_cast hp1) (by norm_num : (0 : ℝ) < 2) (q := 2) ≤ Percolation.theta d p hp1.le := by
-- proof
  apply StatMech.FK.fkTheta_two_le_bernoulliTheta G p hp0 hp1

/--
[pcv_siteEmbed_castAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_siteEmbed_castAdd_eq
  {d : ℕ}
  {k : ℕ}
  {x : Site 2}
  {i : Fin 2} :
-- imply
  pcv_siteEmbed k x (Fin.castAdd k i) = x i := by
-- proof
  apply StatMech.Percolation.pcv_siteEmbed_castAdd k x i

/--
[pcv_siteEmbed_natAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_siteEmbed_natAdd_eq
  {d : ℕ}
  {k : ℕ}
  {x : Site 2}
  {i : Fin k} :
-- imply
  pcv_siteEmbed k x (Fin.natAdd 2 i) = 0 := by
-- proof
  apply StatMech.Percolation.pcv_siteEmbed_natAdd k x i

/--
[pcv_siteEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_siteEmbed_injective_eq
  {d : ℕ}
  {k : ℕ} :
-- imply
  Function.Injective (pcv_siteEmbed k) := by
-- proof
  apply StatMech.Percolation.pcv_siteEmbed_injective k

/--
[pcv_siteEmbed_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_siteEmbed_adj_iff_eq
  {d : ℕ}
  {k : ℕ}
  {x y : Site 2} :
-- imply
  (hypercubicLattice (2 + k)).Adj (pcv_siteEmbed k x) (pcv_siteEmbed k y) ↔ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.Percolation.pcv_siteEmbed_adj_iff k x y

/--
[pcv_edgeEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_edgeEmbed_injective_eq
  {d : ℕ}
  {k : ℕ} :
-- imply
  Function.Injective (pcv_edgeEmbed k) := by
-- proof
  apply StatMech.Percolation.pcv_edgeEmbed_injective k

/--
[bernoulliProduct_map_planeRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma bernoulliProduct_map_planeRestrict_eq
  {d : ℕ}
  {k : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map (pcv_planeRestrict k) (bernoulliProductMeasure (E := Sym2 (Site (2 + k))) p hp) = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp := by
-- proof
  apply StatMech.Percolation.bernoulliProduct_map_planeRestrict k p hp

/--
[pcv_siteEmbed_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_siteEmbed_origin_eq
  {d : ℕ}
  {k : ℕ} :
-- imply
  pcv_siteEmbed k (origin 2) = origin (2 + k) := by
-- proof
  apply StatMech.Percolation.pcv_siteEmbed_origin k

/--
[pcv_connected_of_planeRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_connected_of_planeRestrict_eq
  {d : ℕ}
  {k : ℕ}
  {omega : ConfigSpace (Sym2 (Site (2 + k)))}
  {x y : Site 2}
-- given
  (h : Lattice.Connected 2 (pcv_planeRestrict k omega) x y) :
-- imply
  Lattice.Connected (2 + k) omega (pcv_siteEmbed k x) (pcv_siteEmbed k y) := by
-- proof
  apply StatMech.Percolation.pcv_connected_of_planeRestrict k omega h

/--
[pcv_plane_percolation_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pcv_plane_percolation_subset_eq
  {d : ℕ}
  {k : ℕ} :
-- imply
  pcv_planeRestrict k ⁻¹' percolationEvent 2 ⊆ percolationEvent (2 + k) := by
-- proof
  apply StatMech.Percolation.pcv_plane_percolation_subset k

/--
[theta_two_le_theta_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma theta_two_le_theta_add_eq
  {d : ℕ}
  {k : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  theta 2 p hp ≤ theta (2 + k) p hp := by
-- proof
  apply StatMech.Percolation.theta_two_le_theta_add k p hp

/--
[theta_mono_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma theta_mono_parameter_eq
  {d : ℕ}
  {p q : ℝ≥0}
-- given
  (hp : p ≤ 1)
  (hq : q ≤ 1)
  (hpq : p ≤ q) :
-- imply
  theta d p hp ≤ theta d q hq := by
-- proof
  apply StatMech.Percolation.theta_mono_parameter hp hq hpq

/--
[pc_le_of_theta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pc_le_of_theta_pos_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hpos : 0 < theta d p hp) :
-- imply
  pc d ≤ p := by
-- proof
  apply StatMech.Percolation.pc_le_of_theta_pos p hp hpos

/--
[exists_theta_two_pos_below_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma exists_theta_two_pos_below_one_eq
  {d : ℕ} :
-- imply
  ∃ (p : ℝ≥0) (hp1 : p < 1), 0 < theta 2 p hp1.le := by
-- proof
  apply StatMech.Percolation.exists_theta_two_pos_below_one

/--
[pc_two_lt_one_via_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pc_two_lt_one_via_fk_eq
  {d : ℕ} :
-- imply
  pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pc_two_lt_one_via_fk

/--
[pc_two_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pc_two_nontrivial_eq
  {d : ℕ} :
-- imply
  0 < pc 2 ∧ pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pc_two_nontrivial

/--
[pc_lt_one_of_two_le_via_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pc_lt_one_of_two_le_via_fk_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  pc d < 1 := by
-- proof
  apply StatMech.Percolation.pc_lt_one_of_two_le_via_fk hd

/--
[pc_nontrivial_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean)
-/
@[path]
private lemma pc_nontrivial_of_two_le_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 < pc d ∧ pc d < 1 := by
-- proof
  apply StatMech.Percolation.pc_nontrivial_of_two_le hd


-- created on 2026-10-23
