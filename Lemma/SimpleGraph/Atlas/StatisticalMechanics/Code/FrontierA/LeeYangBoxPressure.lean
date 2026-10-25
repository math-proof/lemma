import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangBoxPressure.Part3
open Finset Filter Topology Set SimpleGraph StatMech StatMech.FrontierA


/--
[bond_abs_le_one_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma bond_abs_le_one_general_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  |bond s e| ≤ 1 := by
-- proof
  apply StatMech.FrontierA.bond_abs_le_one_general s e

/--
[isingHamiltonian_sub_abs_le_edgeDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingHamiltonian_sub_abs_le_edgeDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {s : ConfigSpace V}
-- given
  (hHG : H ≤ G)
  (h : ℝ) :
-- imply
  |hamiltonian G h s - hamiltonian H h s| ≤ (G.edgeFinset \ H.edgeFinset).card := by
-- proof
  apply StatMech.FrontierA.isingHamiltonian_sub_abs_le_edgeDiff G H hHG h s

/--
[isingLogZ_sub_abs_le_edgeDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingLogZ_sub_abs_le_edgeDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
-- given
  (hHG : H ≤ G)
  (beta h : ℝ) :
-- imply
  |Real.log (isingZ G beta h) - Real.log (isingZ H beta h)| ≤ |beta| * (G.edgeFinset \ H.edgeFinset).card := by
-- proof
  apply StatMech.FrontierA.isingLogZ_sub_abs_le_edgeDiff G H hHG beta h

/--
[isingSum_edgeCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingSum_edgeCard_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj] :
-- imply
  (G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
-- proof
  apply StatMech.FrontierA.isingSum_edgeCard G H

/--
[agl_interfaceCard_add_edgeCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma agl_interfaceCard_add_edgeCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
-- given
  (P : V → Prop) :
-- imply
  agl_interfaceCard G P + (agl_left G P).edgeFinset.card + (agl_right G P).edgeFinset.card = G.edgeFinset.card := by
-- proof
  apply StatMech.FrontierA.agl_interfaceCard_add_edgeCards G P

/--
[isingLogZ_partition_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingLogZ_partition_sub_abs_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred P]
-- given
  (P : V → Prop)
  (beta h : ℝ) :
-- imply
  |Real.log (isingZ G beta h) - (Real.log (isingZ (agl_left G P) beta h) + Real.log (isingZ (agl_right G P) beta h))| ≤ |beta| * agl_interfaceCard G P := by
-- proof
  apply StatMech.FrontierA.isingLogZ_partition_sub_abs_le G P beta h

/--
[isingZ_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingZ_empty_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [IsEmpty W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
-- given
  (beta h : ℝ) :
-- imply
  isingZ G beta h = 1 := by
-- proof
  apply StatMech.FrontierA.isingZ_empty G beta h

/--
[isingZ_left_tag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingZ_left_tag_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq T]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {tag : V → T}
  {tau : T}
  {S : Finset T}
-- given
  (htau : tau ∉ S)
  (beta h : ℝ) :
-- imply
  isingZ (agl_left (qp_restG G tag (insert tau S)) (fun x => tag x.1 = tau)) beta h = isingZ (qp_blkG G tag tau) beta h := by
-- proof
  apply StatMech.FrontierA.isingZ_left_tag G tag tau S htau beta h

/--
[isingZ_right_tag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingZ_right_tag_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq T]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {tag : V → T}
  {tau : T}
  {S : Finset T}
-- given
  (htau : tau ∉ S)
  (beta h : ℝ) :
-- imply
  isingZ (agl_right (qp_restG G tag (insert tau S)) (fun x => tag x.1 = tau)) beta h = isingZ (qp_restG G tag S) beta h := by
-- proof
  apply StatMech.FrontierA.isingZ_right_tag G tag tau S htau beta h

/--
[isingLogZ_tagPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingLogZ_tagPeel_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq T]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {tag : V → T}
-- given
  (beta h : ℝ) :
-- imply
  ∀ S : Finset T, ∃ I : ℕ, |Real.log (isingZ (qp_restG G tag S) beta h) - ∑ tau ∈ S, Real.log (isingZ (qp_blkG G tag tau) beta h)| ≤ |beta| * I ∧ I + ∑ tau ∈ S, (qp_blkG G tag tau).edgeFinset.card = (qp_restG G tag S).edgeFinset.card := by
-- proof
  apply StatMech.FrontierA.isingLogZ_tagPeel G tag beta h

/--
[isingLogZ_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingLogZ_abs_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (beta h : ℝ) :
-- imply
  |Real.log (isingZ G beta h)| ≤ (Fintype.card V : ℝ) * Real.log 2 + |beta| * ((G.edgeFinset.card : ℝ) + |h| * Fintype.card V) := by
-- proof
  apply StatMech.FrontierA.isingLogZ_abs_le G beta h

/--
[ising_vanHove_none_vertex_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma ising_vanHove_none_vertex_card_eq
  [Fintype V]
  [DecidableEq V]
  {d m n : ℕ} :
-- imply
  Fintype.card {x : boxVerts d n // ecz_vanHoveTag m n x = none} + (ecz_T m n) ^ d * Fintype.card (boxVerts d m) = Fintype.card (boxVerts d n) := by
-- proof
  apply StatMech.FrontierA.ising_vanHove_none_vertex_card d m n

/--
[isingZ_cellBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingZ_cellBlock_eq
  [Fintype V]
  [DecidableEq V]
  {d m n : ℕ}
  {c : Fin d → Fin (ecz_T m n)}
-- given
  (beta h : ℝ) :
-- imply
  isingZ (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)) beta h = isingZ (boxGraph d m) beta h := by
-- proof
  apply StatMech.FrontierA.isingZ_cellBlock d m n c beta h

/--
[isingBoxLogZ_vanHove_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBoxLogZ_vanHove_abs_le_eq
  [Fintype V]
  [DecidableEq V]
  {d m n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  |isingBoxLogZ d beta h n - ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| ≤ (Real.log 2 + |beta| * |h|) * ((Fintype.card (boxVerts d n) : ℝ) - ((ecz_T m n) ^ d : ℝ) * Fintype.card (boxVerts d m)) + |beta| * (((boxGraph d n).edgeFinset.card : ℝ) - ((ecz_T m n) ^ d : ℝ) * (boxGraph d m).edgeFinset.card) := by
-- proof
  apply StatMech.FrontierA.isingBoxLogZ_vanHove_abs_le d m n beta h

/--
[isingBox_vertexBulkFraction_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBox_vertexBulkFraction_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d m : ℕ} :
-- imply
  Tendsto (fun n => ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) / (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds 1) := by
-- proof
  apply StatMech.FrontierA.isingBox_vertexBulkFraction_tendsto d m

/--
[isingBox_edge_div_vertex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBox_edge_div_vertex_eq_eq
  [Fintype V]
  [DecidableEq V]
  {d n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ((boxGraph d n).edgeFinset.card : ℝ) / (Fintype.card (boxVerts d n) : ℝ) = (d : ℝ) * (2 * (n : ℝ)) / (2 * n + 1) := by
-- proof
  apply StatMech.FrontierA.isingBox_edge_div_vertex_eq d n hd

/--
[isingBox_edgeDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBox_edgeDensity_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) / (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds (d : ℝ)) := by
-- proof
  apply StatMech.FrontierA.isingBox_edgeDensity_tendsto d hd

/--
[isingBox_bulkEdgeDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBox_bulkEdgeDensity_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d m : ℕ} :
-- imply
  Tendsto (fun n => ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds (((boxGraph d m).edgeFinset.card : ℝ) / (Fintype.card (boxVerts d m) : ℝ))) := by
-- proof
  apply StatMech.FrontierA.isingBox_bulkEdgeDensity_tendsto d m

/--
[isingBox_edgeDeficitDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBox_edgeDeficitDensity_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d m : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => (((boxGraph d n).edgeFinset.card : ℝ) - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) / (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds ((d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) / (Fintype.card (boxVerts d m) : ℝ))) := by
-- proof
  apply StatMech.FrontierA.isingBox_edgeDeficitDensity_tendsto d m hd

/--
[isingBox_edgeSurface_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBox_edgeSurface_eq_eq
  [Fintype V]
  [DecidableEq V]
  {d m : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) / (Fintype.card (boxVerts d m) : ℝ) = (d : ℝ) / (2 * (m : ℝ) + 1) := by
-- proof
  apply StatMech.FrontierA.isingBox_edgeSurface_eq d m hd

/--
[isingBox_edgeSurface_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBox_edgeSurface_tendsto_zero_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ} :
-- imply
  Tendsto (fun m : ℕ => (d : ℝ) / (2 * (m : ℝ) + 1)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingBox_edgeSurface_tendsto_zero d

/--
[isingBoxPressure_vanHove_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBoxPressure_vanHove_abs_le_eq
  [Fintype V]
  [DecidableEq V]
  {d m n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  |isingBoxPressureSeq d beta h n - (((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) / (Fintype.card (boxVerts d n) : ℝ)) * isingBoxPressureSeq d beta h m| ≤ (Real.log 2 + |beta| * |h|) * (1 - ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) / (Fintype.card (boxVerts d n) : ℝ)) + |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) / (Fintype.card (boxVerts d n) : ℝ)) := by
-- proof
  apply StatMech.FrontierA.isingBoxPressure_vanHove_abs_le d m n beta h

/--
[isingBoxPressure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBoxPressure_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  ∃ pressure : ℝ, Tendsto (isingBoxPressureSeq d beta h) atTop (nhds pressure) := by
-- proof
  apply StatMech.FrontierA.isingBoxPressure_tendsto d hd beta h

/--
[isingZ_zeroField_eq_exp_mul_fkZEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingZ_zeroField_eq_exp_mul_fkZEdge_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  isingZ G beta 0 = Real.exp (beta * G.edgeFinset.card) * ecz_fkZEdge G (1 - Real.exp (-2 * beta)) 2 := by
-- proof
  apply StatMech.FrontierA.isingZ_zeroField_eq_exp_mul_fkZEdge G beta

/--
[isingBoxLogZ_zeroField_eq_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma isingBoxLogZ_zeroField_eq_fk_eq
  [Fintype V]
  [DecidableEq V]
  {d n : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  isingBoxLogZ d beta 0 n = beta * ((boxGraph d n).edgeFinset.card : ℝ) - ecz_u d (fsc_logit (1 - Real.exp (-2 * beta))) n := by
-- proof
  apply StatMech.FrontierA.isingBoxLogZ_zeroField_eq_fk d n hbeta

/--
[sctBoxGraph_pressure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma sctBoxGraph_pressure_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  ∃ pressure : ℝ, Tendsto (fun n => Real.log (isingZ (sctBoxGraph d n) beta h) / (Fintype.card (sctBox d n) : ℝ)) atTop (nhds pressure) := by
-- proof
  apply StatMech.FrontierA.sctBoxGraph_pressure_tendsto d hd beta h

/--
[freeBox_fvZ_pressure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma freeBox_fvZ_pressure_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  ∃ pressure : ℝ, Tendsto (fun n => Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) / ((boxFinset d n).card : ℝ)) atTop (nhds pressure) := by
-- proof
  apply StatMech.FrontierA.freeBox_fvZ_pressure_tendsto d hd beta h

/--
[leeYangComplexFieldPartition_real_pressure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma leeYangComplexFieldPartition_real_pressure_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  ∃ pressure : ℝ, Tendsto (fun n => Real.log (leeYangComplexFieldPartition (boxGraph d n) beta (h : ℂ)).re / (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds pressure) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexFieldPartition_real_pressure_tendsto d hd beta h

/--
[leeYangBox_pressure_and_logDerivative_analytic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean)
-/
@[path]
private lemma leeYangBox_pressure_and_logDerivative_analytic_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 ≤ beta)
  (h : ℝ) :
-- imply
  (∃ pressure : ℝ, Tendsto (isingBoxPressureSeq d beta h) atTop (nhds pressure)) ∧ ∀ n, AnalyticOnNhd ℂ (leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) {z : ℂ | z.re ≠ 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_pressure_and_logDerivative_analytic d hd beta hbeta h


-- created on 2026-10-23
