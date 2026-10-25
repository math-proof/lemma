import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
open StatMech StatMech.FrontierA


/--
[kwPortChainState_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortChainState_zero_eq
  {n : ℕ}
  {b : Fin n → Fin 2} :
-- imply
  kwPortChainState b 0 = 0 := by
-- proof
  apply StatMech.FrontierA.kwPortChainState_zero b

/--
[kwPortChainState_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortChainState_succ_eq
  {n : ℕ}
  {b : Fin n → Fin 2}
  {i : Fin n} :
-- imply
  kwPortChainState b i.succ = kwPortChainState b i.castSucc + b i := by
-- proof
  apply StatMech.FrontierA.kwPortChainState_succ b i

/--
[kwPortChainState_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortChainState_unique_eq
  {n : ℕ}
  {b : Fin n → Fin 2}
  {y : Fin (n + 1) → Fin 2}
-- given
  (hy0 : y 0 = 0)
  (hrec : ∀ i : Fin n, y i.succ = y i.castSucc + b i) :
-- imply
  y = kwPortChainState b := by
-- proof
  apply StatMech.FrontierA.kwPortChainState_unique b y hy0 hrec

/--
[kw_fin_two_self_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kw_fin_two_self_add_eq
  {x : Fin 2} :
-- imply
  x + x = 0 := by
-- proof
  apply StatMech.FrontierA.kw_fin_two_self_add x

/--
[kwPortChain_sum_eq_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortChain_sum_eq_endpoints_eq
  {n : ℕ}
  {b : Fin n → Fin 2}
  {y : Fin (n + 1) → Fin 2}
-- given
  (hrec : ∀ i : Fin n, y i.succ = y i.castSucc + b i) :
-- imply
  (∑ i, b i) = y 0 + y (Fin.last n) := by
-- proof
  apply StatMech.FrontierA.kwPortChain_sum_eq_endpoints b y hrec

/--
[kwPortChainState_last_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortChainState_last_eq_zero_iff_eq
  {n : ℕ}
  {b : Fin n → Fin 2} :
-- imply
  kwPortChainState b (Fin.last n) = 0 ↔ (∑ i, b i) = 0 := by
-- proof
  apply StatMech.FrontierA.kwPortChainState_last_eq_zero_iff b

/--
[kwPortChain_existsUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortChain_existsUnique_eq
  {n : ℕ}
  {b : Fin n → Fin 2} :
-- imply
  (∑ i, b i) = 0 ↔ ∃! y : Fin (n + 1) → Fin 2, KWPortChainEven b y := by
-- proof
  apply StatMech.FrontierA.kwPortChain_existsUnique b

/--
[kwDartOfPort_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartOfPort_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : KWDartPort G} :
-- imply
  (kwDartOfPort G p).fst = p.1 := by
-- proof
  apply StatMech.FrontierA.kwDartOfPort_fst G p

/--
[kwDartOfPort_portOfDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartOfPort_portOfDart_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : G.Dart} :
-- imply
  kwDartOfPort G (kwPortOfDart G d) = d := by
-- proof
  apply StatMech.FrontierA.kwDartOfPort_portOfDart G d

/--
[kwPortOfDart_dartOfPort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortOfDart_dartOfPort_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : KWDartPort G} :
-- imply
  kwPortOfDart G (kwDartOfPort G p) = p := by
-- proof
  apply StatMech.FrontierA.kwPortOfDart_dartOfPort G p

/--
[kwDartOfPort_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartOfPort_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Function.Injective (kwDartOfPort G) := by
-- proof
  apply StatMech.FrontierA.kwDartOfPort_injective G

/--
[kwDartPort_eq_of_fst_of_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartPort_eq_of_fst_of_val_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : KWDartPort G}
-- given
  (hfst : p.1 = q.1)
  (hidx : p.2.val = q.2.val) :
-- imply
  p = q := by
-- proof
  apply StatMech.FrontierA.kwDartPort_eq_of_fst_of_val G hfst hidx

/--
[kwDartPortSplitGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartPortSplitGraph_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : KWDartPort G} :
-- imply
  (kwDartPortSplitGraph G).Adj p q ↔ kwDartOfPort G q = (kwDartOfPort G p).symm ∨ (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) := by
-- proof
  apply StatMech.FrontierA.kwDartPortSplitGraph_adj G p q

/--
[kwDartPortSplitGraph_degree_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartPortSplitGraph_degree_le_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : KWDartPort G} :
-- imply
  (kwDartPortSplitGraph G).degree p ≤ 3 := by
-- proof
  apply StatMech.FrontierA.kwDartPortSplitGraph_degree_le_three G p

/--
[KWStraightLineEmbedding.outgoing_dartAngle_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma outgoing_dartAngle_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : G.Dart}
-- given
  (hfst : d.fst = e.fst)
  (hne : d ≠ e) :
-- imply
  embedding.dartAngle d ≠ embedding.dartAngle e := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.outgoing_dartAngle_ne embedding hfst hne

/--
[kwAngularPortOrder_rank_lt_of_angle_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularPortOrder_rank_lt_of_angle_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p q : KWDartPort G}
-- given
  (hfst : p.1 = q.1)
  (hangle : (embedding.dartAngle (kwDartOfPort G p)).toReal < (embedding.dartAngle (kwDartOfPort G q)).toReal) :
-- imply
  kwOrderedPortRank (kwAngularPortOrder embedding) p < kwOrderedPortRank (kwAngularPortOrder embedding) q := by
-- proof
  apply StatMech.FrontierA.kwAngularPortOrder_rank_lt_of_angle_lt embedding hfst hangle

/--
[kwAngularPortOrder_rank_lt_iff_angle_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularPortOrder_rank_lt_iff_angle_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p q : KWDartPort G}
-- given
  (hfst : p.1 = q.1) :
-- imply
  kwOrderedPortRank (kwAngularPortOrder embedding) p < kwOrderedPortRank (kwAngularPortOrder embedding) q ↔ (embedding.dartAngle (kwDartOfPort G p)).toReal < (embedding.dartAngle (kwDartOfPort G q)).toReal := by
-- proof
  apply StatMech.FrontierA.kwAngularPortOrder_rank_lt_iff_angle_lt embedding hfst

/--
[kw_oppositeTurn_toReal_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kw_oppositeTurn_toReal_of_lt_eq
  {a b : Real.Angle}
-- given
  (h : a.toReal < b.toReal) :
-- imply
  (b - (a + (Real.pi : Real.Angle))).toReal = b.toReal - a.toReal - Real.pi := by
-- proof
  apply StatMech.FrontierA.kw_oppositeTurn_toReal_of_lt a b h

/--
[kw_oppositeTurn_toReal_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kw_oppositeTurn_toReal_of_gt_eq
  {a b : Real.Angle}
-- given
  (h : b.toReal < a.toReal) :
-- imply
  (b - (a + (Real.pi : Real.Angle))).toReal = b.toReal - a.toReal + Real.pi := by
-- proof
  apply StatMech.FrontierA.kw_oppositeTurn_toReal_of_gt a b h

/--
[kwPortAngleRoot_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortAngleRoot_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p : KWDartPort G} :
-- imply
  kwPortAngleRoot embedding p ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwPortAngleRoot_ne_zero embedding p

/--
[KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma turnPhase_eq_portRoots_of_rank_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : G.Dart}
-- given
  (hde : d.snd = e.fst)
  (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G d.symm) < kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G e)) :
-- imply
  embedding.turnPhase d e = -Complex.I * (kwPortAngleRoot embedding (kwPortOfDart G d.symm))⁻¹ * kwPortAngleRoot embedding (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_lt embedding d e hde hrank

/--
[KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma turnPhase_eq_portRoots_of_rank_gt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : G.Dart}
-- given
  (hde : d.snd = e.fst)
  (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G e) < kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G d.symm)) :
-- imply
  embedding.turnPhase d e = Complex.I * (kwPortAngleRoot embedding (kwPortOfDart G d.symm))⁻¹ * kwPortAngleRoot embedding (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.turnPhase_eq_portRoots_of_rank_gt embedding d e hde hrank

/--
[kwOrderedDartPortSplitGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedDartPortSplitGraph_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p q : KWDartPort G} :
-- imply
  (kwOrderedDartPortSplitGraph G order).Adj p q ↔ kwDartOfPort G q = (kwDartOfPort G p).symm ∨ (p.1 = q.1 ∧ (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨ kwOrderedPortRank order q + 1 = kwOrderedPortRank order p)) := by
-- proof
  apply StatMech.FrontierA.kwOrderedDartPortSplitGraph_adj G order p q

/--
[kwOrderedExternalSplitDartOfDart_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedExternalSplitDartOfDart_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : G.Dart} :
-- imply
  (kwOrderedExternalSplitDartOfDart G order d).1.fst = kwPortOfDart G d := by
-- proof
  apply StatMech.FrontierA.kwOrderedExternalSplitDartOfDart_fst G order d

/--
[kwOrderedExternalSplitDartOfDart_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedExternalSplitDartOfDart_snd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : G.Dart} :
-- imply
  (kwOrderedExternalSplitDartOfDart G order d).1.snd = kwPortOfDart G d.symm := by
-- proof
  apply StatMech.FrontierA.kwOrderedExternalSplitDartOfDart_snd G order d

/--
[kwOrderedSplitDartBlockEquiv_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitDartBlockEquiv_inl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : G.Dart} :
-- imply
  kwOrderedSplitDartBlockEquiv G order (Sum.inl d) = (kwOrderedExternalSplitDartOfDart G order d).1 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitDartBlockEquiv_inl G order d

/--
[kwOrderedSplitDartBlockEquiv_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitDartBlockEquiv_inr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : KWOrderedInternalSplitDart G order} :
-- imply
  kwOrderedSplitDartBlockEquiv G order (Sum.inr d) = d.1 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitDartBlockEquiv_inr G order d

/--
[kwOrderedSplitTransitionInBlocks_eq_fromBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitTransitionInBlocks_eq_fromBlocks_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {M : Matrix (kwOrderedDartPortSplitGraph G order).Dart (kwOrderedDartPortSplitGraph G order).Dart ℂ} :
-- imply
  kwOrderedSplitTransitionInBlocks G order M = Matrix.fromBlocks (kwOrderedSplitTransitionInBlocks G order M).toBlocks₁₁ (kwOrderedSplitTransitionInBlocks G order M).toBlocks₁₂ (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₁ (kwOrderedSplitTransitionInBlocks G order M).toBlocks₂₂ := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitTransitionInBlocks_eq_fromBlocks G order M

/--
[kwOrderedSplitTransitionInBlocks_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitTransitionInBlocks_det_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {M : Matrix (kwOrderedDartPortSplitGraph G order).Dart (kwOrderedDartPortSplitGraph G order).Dart ℂ} :
-- imply
  (kwOrderedSplitTransitionInBlocks G order M).det = M.det := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitTransitionInBlocks_det G order M

/--
[kw_pathGraph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kw_pathGraph_edgeFinset_eq
  {n : ℕ} :
-- imply
  (SimpleGraph.pathGraph (n + 1)).edgeFinset = Finset.univ.image (fun i : Fin n ↦ s(i.castSucc, i.succ)) := by
-- proof
  apply StatMech.FrontierA.kw_pathGraph_edgeFinset n

/--
[kw_pathGraph_edgeFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kw_pathGraph_edgeFinset_card_eq
  {n : ℕ} :
-- imply
  (SimpleGraph.pathGraph (n + 1)).edgeFinset.card = n := by
-- proof
  apply StatMech.FrontierA.kw_pathGraph_edgeFinset_card n

/--
[kw_pathGraph_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kw_pathGraph_isAcyclic_eq
  {n : ℕ} :
-- imply
  (SimpleGraph.pathGraph n).IsAcyclic := by
-- proof
  apply StatMech.FrontierA.kw_pathGraph_isAcyclic n

/--
[kwOutgoingDart_card_le_port_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOutgoingDart_card_le_port_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V} :
-- imply
  Fintype.card (KWOutgoingDart (G := G) v) ≤ Fintype.card (KWDartPort G) := by
-- proof
  apply StatMech.FrontierA.kwOutgoingDart_card_le_port_card G v

/--
[kwOrderedPortForestCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedPortForestCode_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G} :
-- imply
  Function.Injective (kwOrderedPortForestCode G order) := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortForestCode_injective G order

/--
[kwOrderedPortInternalGraph_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedPortInternalGraph_isAcyclic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G} :
-- imply
  (kwOrderedPortInternalGraph G order).IsAcyclic := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortInternalGraph_isAcyclic G order

/--
[kwOrderedInternalSplitDartEquiv_toProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalSplitDartEquiv_toProd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {delta : KWOrderedInternalSplitDart G order} :
-- imply
  (kwOrderedInternalSplitDartEquiv G order delta).toProd = delta.1.toProd := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalSplitDartEquiv_toProd G order delta

/--
[kwOrderedInternalSplitDartEquiv_symm_toProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalSplitDartEquiv_symm_toProd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {delta : (kwOrderedPortInternalGraph G order).Dart} :
-- imply
  ((kwOrderedInternalSplitDartEquiv G order).symm delta).1.toProd = delta.toProd := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalSplitDartEquiv_symm_toProd G order delta

/--
[kwOrderedSplitInternalBlock_reindex_eq_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitInternalBlock_reindex_eq_transition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 (KWDartPort G) → ℂ}
  {phase : (kwOrderedDartPortSplitGraph G order).Dart → (kwOrderedDartPortSplitGraph G order).Dart → ℂ} :
-- imply
  Matrix.reindex (kwOrderedInternalSplitDartEquiv G order) (kwOrderedInternalSplitDartEquiv G order) (kwOrderedSplitInternalBlock G order (kwGraphTransition (kwOrderedDartPortSplitGraph G order) weight phase)) = kwGraphTransition (kwOrderedPortInternalGraph G order) weight (kwOrderedInternalPhase G order phase) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitInternalBlock_reindex_eq_transition G order weight phase

/--
[kwOrderedSplitInternalBlock_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitInternalBlock_isNilpotent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 (KWDartPort G) → ℂ}
  {phase : (kwOrderedDartPortSplitGraph G order).Dart → (kwOrderedDartPortSplitGraph G order).Dart → ℂ} :
-- imply
  IsNilpotent (kwOrderedSplitInternalBlock G order (kwGraphTransition (kwOrderedDartPortSplitGraph G order) weight phase)) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitInternalBlock_isNilpotent G order weight phase

/--
[kwOrderedSplit_det_eq_effective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplit_det_eq_effective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 (KWDartPort G) → ℂ}
  {phase : (kwOrderedDartPortSplitGraph G order).Dart → (kwOrderedDartPortSplitGraph G order).Dart → ℂ} :
-- imply
  let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order) weight phase let R := kwOrderedSplitTransitionInBlocks G order M ∃ n : ℕ, (1 - M).det = (1 - kwEliminateAcyclicInternal R.toBlocks₁₁ R.toBlocks₁₂ R.toBlocks₂₁ R.toBlocks₂₂ n).det := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplit_det_eq_effective G order weight phase

/--
[kwOrderedSplit_externalBlock_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplit_externalBlock_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 (KWDartPort G) → ℂ}
  {phase : (kwOrderedDartPortSplitGraph G order).Dart → (kwOrderedDartPortSplitGraph G order).Dart → ℂ} :
-- imply
  (kwOrderedSplitTransitionInBlocks G order (kwGraphTransition (kwOrderedDartPortSplitGraph G order) weight phase)).toBlocks₁₁ = 0 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplit_externalBlock_eq_zero G order weight phase

/--
[kwOrderedSplit_det_eq_pathEffective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplit_det_eq_pathEffective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {weight : Sym2 (KWDartPort G) → ℂ}
  {phase : (kwOrderedDartPortSplitGraph G order).Dart → (kwOrderedDartPortSplitGraph G order).Dart → ℂ} :
-- imply
  let M := kwGraphTransition (kwOrderedDartPortSplitGraph G order) weight phase let R := kwOrderedSplitTransitionInBlocks G order M ∃ n : ℕ, (1 - M).det = (1 - R.toBlocks₁₂ * kwNilpotentResolvent R.toBlocks₂₂ n * R.toBlocks₂₁).det := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplit_det_eq_pathEffective G order weight phase

/--
[kwOrderedSplitWeight_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitWeight_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {order : KWPortOrder G}
  {d : G.Dart} :
-- imply
  kwOrderedSplitWeight G weight (kwOrderedExternalSplitDartOfDart G order d).1.edge = weight d.edge := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitWeight_matching G weight order d

/--
[kwOrderedSplitWeight_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedSplitWeight_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {order : KWPortOrder G}
  {d : KWOrderedInternalSplitDart G order} :
-- imply
  kwOrderedSplitWeight G weight d.1.edge = 1 := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitWeight_internal G weight order d

/--
[kwAngularSplitPhase_external_internal_of_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitPhase_external_internal_of_rank_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) e.1.fst < kwOrderedPortRank (kwAngularPortOrder embedding) e.1.snd) :
-- imply
  kwAngularSplitPhase embedding (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) d).1 e.1 = -Complex.I * (kwPortAngleRoot embedding e.1.fst)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitPhase_external_internal_of_rank_lt embedding d e hrank

/--
[kwAngularSplitPhase_external_internal_of_rank_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitPhase_external_internal_of_rank_gt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) e.1.snd < kwOrderedPortRank (kwAngularPortOrder embedding) e.1.fst) :
-- imply
  kwAngularSplitPhase embedding (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) d).1 e.1 = Complex.I * (kwPortAngleRoot embedding e.1.fst)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitPhase_external_internal_of_rank_gt embedding d e hrank

/--
[kwAngularSplitPhase_internal_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitPhase_internal_external_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart} :
-- imply
  kwAngularSplitPhase embedding d.1 (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) e).1 = kwPortAngleRoot embedding (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitPhase_internal_external embedding d e

/--
[kwAngularSplitPhase_internal_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitPhase_internal_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)} :
-- imply
  kwAngularSplitPhase embedding d.1 e.1 = 1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitPhase_internal_internal embedding d e

/--
[kwAngularSplitPhase_endpointProduct_of_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitPhase_endpointProduct_of_rank_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : G.Dart}
  {first last : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hde : d.snd = e.fst)
  (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G d.symm) < kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G e))
  (hfirst : first.1.fst = kwPortOfDart G d.symm)
  (hfirstRank : kwOrderedPortRank (kwAngularPortOrder embedding) first.1.fst < kwOrderedPortRank (kwAngularPortOrder embedding) first.1.snd) :
-- imply
  kwAngularSplitPhase embedding (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) d).1 first.1 * kwAngularSplitPhase embedding last.1 (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) e).1 = embedding.turnPhase d e := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitPhase_endpointProduct_of_rank_lt embedding d e hde hrank first last hfirst hfirstRank

/--
[kwAngularSplitPhase_endpointProduct_of_rank_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitPhase_endpointProduct_of_rank_gt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d e : G.Dart}
  {first last : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hde : d.snd = e.fst)
  (hrank : kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G e) < kwOrderedPortRank (kwAngularPortOrder embedding) (kwPortOfDart G d.symm))
  (hfirst : first.1.fst = kwPortOfDart G d.symm)
  (hfirstRank : kwOrderedPortRank (kwAngularPortOrder embedding) first.1.snd < kwOrderedPortRank (kwAngularPortOrder embedding) first.1.fst) :
-- imply
  kwAngularSplitPhase embedding (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) d).1 first.1 * kwAngularSplitPhase embedding last.1 (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) e).1 = embedding.turnPhase d e := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitPhase_endpointProduct_of_rank_gt embedding d e hde hrank first last hfirst hfirstRank

/--
[kwAngularSplit_internalPhase_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_internalPhase_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  kwOrderedInternalPhase G (kwAngularPortOrder embedding) (kwAngularSplitPhase embedding) = fun _ _ ↦ 1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_internalPhase_eq_one embedding

/--
[kwDartPort_eq_of_fst_of_orderRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartPort_eq_of_fst_of_orderRank_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p q : KWDartPort G}
-- given
  (hfst : p.1 = q.1)
  (hidx : kwOrderedPortRank order p = kwOrderedPortRank order q) :
-- imply
  p = q := by
-- proof
  apply StatMech.FrontierA.kwDartPort_eq_of_fst_of_orderRank order hfst hidx

/--
[kwOrderedInternalSplitDart_adj_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalSplitDart_adj_data_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : KWOrderedInternalSplitDart G order} :
-- imply
  d.1.fst.1 = d.1.snd.1 ∧ (kwOrderedPortRank order d.1.fst + 1 = kwOrderedPortRank order d.1.snd ∨ kwOrderedPortRank order d.1.snd + 1 = kwOrderedPortRank order d.1.fst) := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalSplitDart_adj_data G order d

/--
[kwOrderedInternalDartStep_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartStep_rank_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d e : KWOrderedInternalSplitDart G order}
-- given
  (hstep : KWOrderedInternalDartStep G order d e)
  (hd : kwOrderedPortRank order d.1.fst < kwOrderedPortRank order d.1.snd) :
-- imply
  kwOrderedPortRank order e.1.fst < kwOrderedPortRank order e.1.snd := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartStep_rank_lt G order hstep hd

/--
[kwOrderedInternalDartStep_rank_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartStep_rank_gt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d e : KWOrderedInternalSplitDart G order}
-- given
  (hstep : KWOrderedInternalDartStep G order d e)
  (hd : kwOrderedPortRank order d.1.snd < kwOrderedPortRank order d.1.fst) :
-- imply
  kwOrderedPortRank order e.1.snd < kwOrderedPortRank order e.1.fst := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartStep_rank_gt G order hstep hd

/--
[kwOrderedInternalDartStep_rightUnique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartStep_rightUnique_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d e f : KWOrderedInternalSplitDart G order}
-- given
  (he : KWOrderedInternalDartStep G order d e)
  (hf : KWOrderedInternalDartStep G order d f) :
-- imply
  e = f := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartStep_rightUnique G order he hf

/--
[kwOrderedInternalDartFacesPort_of_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartFacesPort_of_snd_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : KWOrderedInternalSplitDart G order}
  {q : KWDartPort G}
-- given
  (h : d.1.snd = q) :
-- imply
  KWOrderedInternalDartFacesPort order d q := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartFacesPort_of_snd_eq G order d q h

/--
[kwOrderedInternalDartFacesPort_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartFacesPort_of_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d e : KWOrderedInternalSplitDart G order}
  {q : KWDartPort G}
-- given
  (hstep : KWOrderedInternalDartStep G order d e)
  (heq : KWOrderedInternalDartFacesPort order e q) :
-- imply
  KWOrderedInternalDartFacesPort order d q := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartFacesPort_of_step G order hstep heq

/--
[kwOrderedInternalDartFacesPort_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartFacesPort_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d e : KWOrderedInternalSplitDart G order}
  {q : KWDartPort G}
-- given
  (hstep : KWOrderedInternalDartStep G order d e)
  (hdq : KWOrderedInternalDartFacesPort order d q)
  (hne : d.1.snd ≠ q) :
-- imply
  KWOrderedInternalDartFacesPort order e q := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartFacesPort_step G order hstep hdq hne

/--
[kwOrderedInternalDartStep_not_faces_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartStep_not_faces_snd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d e : KWOrderedInternalSplitDart G order}
-- given
  (hstep : KWOrderedInternalDartStep G order d e) :
-- imply
  ¬KWOrderedInternalDartFacesPort order e d.1.snd := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartStep_not_faces_snd G order hstep

/--
[kwOrderedInternalDart_not_faces_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDart_not_faces_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : KWOrderedInternalSplitDart G order} :
-- imply
  ¬KWOrderedInternalDartFacesPort order d d.1.fst := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDart_not_faces_fst G order d

/--
[kwOrderedInternalDart_eq_of_fst_eq_of_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDart_eq_of_fst_eq_of_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d e : KWOrderedInternalSplitDart G order}
  {q : KWDartPort G}
-- given
  (hfst : d.1.fst = e.1.fst)
  (hdq : KWOrderedInternalDartFacesPort order d q)
  (heq : KWOrderedInternalDartFacesPort order e q) :
-- imply
  d = e := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDart_eq_of_fst_eq_of_faces G order hfst hdq heq

/--
[kwOrderedPortAtRank_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedPortAtRank_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {v : V}
-- given
  (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) :
-- imply
  (kwOrderedPortAtRank order v i).1 = v := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortAtRank_fst order v i

/--
[kwOrderedPortAtRank_rank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedPortAtRank_rank_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {v : V}
-- given
  (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) :
-- imply
  kwOrderedPortRank order (kwOrderedPortAtRank order v i) = i.val := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortAtRank_rank order v i

/--
[kwOrderedIncreasingInternalDartFrom_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedIncreasingInternalDartFrom_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G}
-- given
  (h : kwOrderedPortRank order p + 1 < Fintype.card (KWOutgoingDart (G := G) p.1)) :
-- imply
  (kwOrderedIncreasingInternalDartFrom G order p h).1.fst = p := by
-- proof
  apply StatMech.FrontierA.kwOrderedIncreasingInternalDartFrom_fst G order p h

/--
[kwOrderedIncreasingInternalDartFrom_rank_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedIncreasingInternalDartFrom_rank_snd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G}
-- given
  (h : kwOrderedPortRank order p + 1 < Fintype.card (KWOutgoingDart (G := G) p.1)) :
-- imply
  kwOrderedPortRank order (kwOrderedIncreasingInternalDartFrom G order p h).1.snd = kwOrderedPortRank order p + 1 := by
-- proof
  apply StatMech.FrontierA.kwOrderedIncreasingInternalDartFrom_rank_snd G order p h

/--
[kwOrderedDecreasingInternalDartFrom_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedDecreasingInternalDartFrom_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G}
-- given
  (h : 0 < kwOrderedPortRank order p) :
-- imply
  (kwOrderedDecreasingInternalDartFrom G order p h).1.fst = p := by
-- proof
  apply StatMech.FrontierA.kwOrderedDecreasingInternalDartFrom_fst G order p h

/--
[kwOrderedDecreasingInternalDartFrom_rank_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedDecreasingInternalDartFrom_rank_snd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G}
-- given
  (h : 0 < kwOrderedPortRank order p) :
-- imply
  kwOrderedPortRank order (kwOrderedDecreasingInternalDartFrom G order p h).1.snd + 1 = kwOrderedPortRank order p := by
-- proof
  apply StatMech.FrontierA.kwOrderedDecreasingInternalDartFrom_rank_snd G order p h

/--
[kwOrderedIncreasingInternalDartFrom_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedIncreasingInternalDartFrom_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p q : KWDartPort G}
-- given
  (hpq : p.1 = q.1)
  (hlt : kwOrderedPortRank order p < kwOrderedPortRank order q)
  (hbound : kwOrderedPortRank order p + 1 < Fintype.card (KWOutgoingDart (G := G) p.1)) :
-- imply
  KWOrderedInternalDartFacesPort order (kwOrderedIncreasingInternalDartFrom G order p hbound) q := by
-- proof
  apply StatMech.FrontierA.kwOrderedIncreasingInternalDartFrom_faces G order p q hpq hlt hbound

/--
[kwOrderedDecreasingInternalDartFrom_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedDecreasingInternalDartFrom_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p q : KWDartPort G}
-- given
  (hpq : p.1 = q.1)
  (hlt : kwOrderedPortRank order q < kwOrderedPortRank order p)
  (hbound : 0 < kwOrderedPortRank order p) :
-- imply
  KWOrderedInternalDartFacesPort order (kwOrderedDecreasingInternalDartFrom G order p hbound) q := by
-- proof
  apply StatMech.FrontierA.kwOrderedDecreasingInternalDartFrom_faces G order p q hpq hlt hbound

/--
[kwOrderedInternalDartStep_increasingFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartStep_increasingFrom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : KWOrderedInternalSplitDart G order}
-- given
  (hd : kwOrderedPortRank order d.1.fst < kwOrderedPortRank order d.1.snd)
  (hbound : kwOrderedPortRank order d.1.snd + 1 < Fintype.card (KWOutgoingDart (G := G) d.1.snd.1)) :
-- imply
  KWOrderedInternalDartStep G order d (kwOrderedIncreasingInternalDartFrom G order d.1.snd hbound) := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartStep_increasingFrom G order d hd hbound

/--
[kwOrderedInternalDartStep_decreasingFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedInternalDartStep_decreasingFrom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : KWOrderedInternalSplitDart G order}
-- given
  (hd : kwOrderedPortRank order d.1.snd < kwOrderedPortRank order d.1.fst)
  (hbound : 0 < kwOrderedPortRank order d.1.snd) :
-- imply
  KWOrderedInternalDartStep G order d (kwOrderedDecreasingInternalDartFrom G order d.1.snd hbound) := by
-- proof
  apply StatMech.FrontierA.kwOrderedInternalDartStep_decreasingFrom G order d hd hbound

/--
[kwAngularSplit_internalBlock_apply_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_internalBlock_apply_of_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hstep : KWOrderedInternalDartStep G (kwAngularPortOrder embedding) d e) :
-- imply
  kwOrderedSplitInternalBlock G (kwAngularPortOrder embedding) (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)) d e = 1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_internalBlock_apply_of_step embedding weight d e hstep

/--
[kwAngularSplit_internalBlock_apply_of_not_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_internalBlock_apply_of_not_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hstep : ¬KWOrderedInternalDartStep G (kwAngularPortOrder embedding) d e) :
-- imply
  kwOrderedSplitInternalBlock G (kwAngularPortOrder embedding) (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_internalBlock_apply_of_not_step embedding weight d e hstep

/--
[kwOrderedExternalSplitDart_edge_ne_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedExternalSplitDart_edge_ne_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G order} :
-- imply
  (kwOrderedExternalSplitDartOfDart G order d).1.edge ≠ e.1.edge := by
-- proof
  apply StatMech.FrontierA.kwOrderedExternalSplitDart_edge_ne_internal G order d e

/--
[kwAngularSplit_enterBlock_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_enterBlock_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hconnect : kwPortOfDart G d.symm = e.1.fst) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding) (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding))).toBlocks₁₂ d e = weight d.edge * kwAngularSplitPhase embedding (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) d).1 e.1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_enterBlock_apply_of_connect embedding weight d e hconnect

/--
[kwAngularSplit_enterBlock_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_enterBlock_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding) (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding))).toBlocks₁₂ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_enterBlock_apply_of_not_connect embedding weight d e hconnect

/--
[kwAngularSplit_exitBlock_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_exitBlock_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd = kwPortOfDart G e) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding) (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding))).toBlocks₂₁ d e = kwPortAngleRoot embedding (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_exitBlock_apply_of_connect embedding weight d e hconnect

/--
[kwAngularSplit_exitBlock_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_exitBlock_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd ≠ kwPortOfDart G e) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (kwAngularPortOrder embedding) (kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding))).toBlocks₂₁ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_exitBlock_apply_of_not_connect embedding weight d e hconnect

/--
[kwAngularSplitBlocks_internal_apply_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitBlocks_internal_apply_of_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hstep : KWOrderedInternalDartStep G (kwAngularPortOrder embedding) d e) :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d e = 1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitBlocks_internal_apply_of_step embedding weight d e hstep

/--
[kwAngularSplitBlocks_internal_apply_of_not_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitBlocks_internal_apply_of_not_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hstep : ¬KWOrderedInternalDartStep G (kwAngularPortOrder embedding) d e) :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₂₂ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitBlocks_internal_apply_of_not_step embedding weight d e hstep

/--
[kwAngularSplitBlocks_enter_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitBlocks_enter_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hconnect : kwPortOfDart G d.symm = e.1.fst) :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d e = weight d.edge * kwAngularSplitPhase embedding (kwOrderedExternalSplitDartOfDart G (kwAngularPortOrder embedding) d).1 e.1 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitBlocks_enter_apply_of_connect embedding weight d e hconnect

/--
[kwAngularSplitBlocks_enter_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitBlocks_enter_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
-- given
  (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₁₂ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitBlocks_enter_apply_of_not_connect embedding weight d e hconnect

/--
[kwAngularSplitBlocks_exit_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitBlocks_exit_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd = kwPortOfDart G e) :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₂₁ d e = kwPortAngleRoot embedding (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitBlocks_exit_apply_of_connect embedding weight d e hconnect

/--
[kwAngularSplitBlocks_exit_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplitBlocks_exit_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd ≠ kwPortOfDart G e) :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₂₁ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitBlocks_exit_apply_of_not_connect embedding weight d e hconnect

/--
[kwAngularInternalExitSolution_of_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularInternalExitSolution_of_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hfaces : KWOrderedInternalDartFacesPort (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
-- imply
  kwAngularInternalExitSolution embedding d e = kwPortAngleRoot embedding (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwAngularInternalExitSolution_of_faces embedding d e hfaces

/--
[kwAngularInternalExitSolution_of_not_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularInternalExitSolution_of_not_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hfaces : ¬KWOrderedInternalDartFacesPort (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
-- imply
  kwAngularInternalExitSolution embedding d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularInternalExitSolution_of_not_faces embedding d e hfaces

/--
[kwAngularSplit_internal_mul_exitSolution_of_faces_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_internal_mul_exitSolution_of_faces_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hfaces : KWOrderedInternalDartFacesPort (kwAngularPortOrder embedding) d (kwPortOfDart G e))
  (hne : d.1.snd ≠ kwPortOfDart G e) :
-- imply
  ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ * kwAngularInternalExitSolution embedding) d e = kwPortAngleRoot embedding (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_internal_mul_exitSolution_of_faces_of_ne embedding weight d e hfaces hne

/--
[kwAngularSplit_internal_mul_exitSolution_of_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_internal_mul_exitSolution_of_snd_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hsnd : d.1.snd = kwPortOfDart G e) :
-- imply
  ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ * kwAngularInternalExitSolution embedding) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_internal_mul_exitSolution_of_snd_eq embedding weight d e hsnd

/--
[kwAngularSplit_internal_mul_exitSolution_of_not_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_internal_mul_exitSolution_of_not_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (kwAngularPortOrder embedding)}
  {e : G.Dart}
-- given
  (hfaces : ¬KWOrderedInternalDartFacesPort (kwAngularPortOrder embedding) d (kwPortOfDart G e)) :
-- imply
  ((kwAngularSplitBlocks embedding weight).toBlocks₂₂ * kwAngularInternalExitSolution embedding) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_internal_mul_exitSolution_of_not_faces embedding weight d e hfaces

/--
[kwAngularSplit_exitSolution_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_exitSolution_equation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ} :
-- imply
  (1 - (kwAngularSplitBlocks embedding weight).toBlocks₂₂) * kwAngularInternalExitSolution embedding = (kwAngularSplitBlocks embedding weight).toBlocks₂₁ := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_exitSolution_equation embedding weight

/--
[kwAngularSplit_resolvent_mul_exit_eq_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_resolvent_mul_exit_eq_solution_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {n : ℕ}
-- given
  (hpow : (kwAngularSplitBlocks embedding weight).toBlocks₂₂ ^ n = 0) :
-- imply
  kwNilpotentResolvent (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n * (kwAngularSplitBlocks embedding weight).toBlocks₂₁ = kwAngularInternalExitSolution embedding := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_resolvent_mul_exit_eq_solution embedding weight n hpow

/--
[kwAngularSplit_enter_mul_exitSolution_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_enter_mul_exitSolution_of_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d e : G.Dart}
-- given
  (hde : d.snd = e.fst)
  (hnb : d.edge ≠ e.edge) :
-- imply
  ((kwAngularSplitBlocks embedding weight).toBlocks₁₂ * kwAngularInternalExitSolution embedding) d e = weight d.edge * embedding.turnPhase d e := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_enter_mul_exitSolution_of_step embedding weight d e hde hnb

/--
[kwAngularSplit_enter_mul_exitSolution_of_not_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_enter_mul_exitSolution_of_not_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {d e : G.Dart}
-- given
  (hstep : ¬(d.snd = e.fst ∧ d.edge ≠ e.edge)) :
-- imply
  ((kwAngularSplitBlocks embedding weight).toBlocks₁₂ * kwAngularInternalExitSolution embedding) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_enter_mul_exitSolution_of_not_step embedding weight d e hstep

/--
[kwAngularSplit_enter_mul_exitSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_enter_mul_exitSolution_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ} :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₁₂ * kwAngularInternalExitSolution embedding = kwGraphTransition G weight embedding.turnPhase := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_enter_mul_exitSolution embedding weight

/--
[kwAngularSplit_pathEffective_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_pathEffective_eq_original_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {n : ℕ}
-- given
  (hpow : (kwAngularSplitBlocks embedding weight).toBlocks₂₂ ^ n = 0) :
-- imply
  (kwAngularSplitBlocks embedding weight).toBlocks₁₂ * kwNilpotentResolvent (kwAngularSplitBlocks embedding weight).toBlocks₂₂ n * (kwAngularSplitBlocks embedding weight).toBlocks₂₁ = kwGraphTransition G weight embedding.turnPhase := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_pathEffective_eq_original embedding weight n hpow

/--
[kwAngularSplit_det_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwAngularSplit_det_eq_original_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ} :
-- imply
  (1 - kwGraphTransition (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwOrderedSplitWeight G weight) (kwAngularSplitPhase embedding)).det = (1 - kwGraphTransition G weight embedding.turnPhase).det := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_det_eq_original embedding weight

/--
[kwOrderedDartPortSplitGraph_degree_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedDartPortSplitGraph_degree_le_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p : KWDartPort G} :
-- imply
  (kwOrderedDartPortSplitGraph G order).degree p ≤ 3 := by
-- proof
  apply StatMech.FrontierA.kwOrderedDartPortSplitGraph_degree_le_three G order p

/--
[kwOrderedDartPortSplitGraph_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedDartPortSplitGraph_identity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  kwOrderedDartPortSplitGraph G (kwIdentityPortOrder G) = kwDartPortSplitGraph G := by
-- proof
  apply StatMech.FrontierA.kwOrderedDartPortSplitGraph_identity G

/--
[kwExternalPortBits_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwExternalPortBits_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {p : KWDartPort G} :
-- imply
  kwExternalPortBits G b (kwPortOfDart G (kwDartOfPort G p).symm) = kwExternalPortBits G b p := by
-- proof
  apply StatMech.FrontierA.kwExternalPortBits_matching G b p

/--
[kwOrderedExternalPortBits_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedExternalPortBits_sum_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {v : V} :
-- imply
  (∑ i, kwExternalPortBits G b (kwPortAtOrderedRank order v i)) = ∑ i, kwExternalPortBits G b ⟨v, i⟩ := by
-- proof
  apply StatMech.FrontierA.kwOrderedExternalPortBits_sum_eq G order b v

/--
[kwOrderedDartPortSplit_existsUnique_internal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedDartPortSplit_existsUnique_internal_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G} :
-- imply
  KWOriginalPortEven G b ↔ ∃! y : KWPortChainField G, KWOrderedGlobalPortChainEven G order b y := by
-- proof
  apply StatMech.FrontierA.kwOrderedDartPortSplit_existsUnique_internal_iff G order b

/--
[kwOrderedPortSplitAdjBit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedPortSplitAdjBit_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {p q : KWDartPort G}
-- given
  (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q) :
-- imply
  kwOrderedPortSplitAdjBit G order b y p q = kwOrderedPortSplitAdjBit G order b y q p := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortSplitAdjBit_symm G order b y hpq

/--
[kwOrderedPortSplitIncidence_eq_zero_of_globalEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOrderedPortSplitIncidence_eq_zero_of_globalEven_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {p : KWDartPort G}
-- given
  (hy : KWOrderedGlobalPortChainEven G order b y) :
-- imply
  kwOrderedPortSplitIncidence G order b y p = 0 := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortSplitIncidence_eq_zero_of_globalEven G order b y hy p

/--
[kwPortSplitAdjBit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortSplitAdjBit_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {p q : KWDartPort G}
-- given
  (hpq : (kwDartPortSplitGraph G).Adj p q) :
-- imply
  kwPortSplitAdjBit G b y p q = kwPortSplitAdjBit G b y q p := by
-- proof
  apply StatMech.FrontierA.kwPortSplitAdjBit_symm G b y hpq

/--
[kwPortSplitIncidence_eq_zero_of_globalEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortSplitIncidence_eq_zero_of_globalEven_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
  {p : KWDartPort G}
-- given
  (hy : KWGlobalPortChainEven G b y) :
-- imply
  kwPortSplitIncidence G b y p = 0 := by
-- proof
  apply StatMech.FrontierA.kwPortSplitIncidence_eq_zero_of_globalEven G b y hy p

/--
[kwDartPortSplit_existsUnique_internal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartPortSplit_existsUnique_internal_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G} :
-- imply
  KWOriginalPortEven G b ↔ ∃! y : KWPortChainField G, KWGlobalPortChainEven G b y := by
-- proof
  apply StatMech.FrontierA.kwDartPortSplit_existsUnique_internal_iff G b

/--
[kwCanonicalPortChainField_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwCanonicalPortChainField_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
-- given
  (hb : KWOriginalPortEven G b) :
-- imply
  KWGlobalPortChainEven G b (kwCanonicalPortChainField G b) := by
-- proof
  apply StatMech.FrontierA.kwCanonicalPortChainField_even G b hb

/--
[kwPortChainField_eq_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwPortChainField_eq_canonical_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
-- given
  (hy : KWGlobalPortChainEven G b y) :
-- imply
  y = kwCanonicalPortChainField G b := by
-- proof
  apply StatMech.FrontierA.kwPortChainField_eq_canonical G b y hy

/--
[kwOriginalPortEven_of_globalPortChainEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwOriginalPortEven_of_globalPortChainEven_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
-- given
  (hy : KWGlobalPortChainEven G b y) :
-- imply
  KWOriginalPortEven G b := by
-- proof
  apply StatMech.FrontierA.kwOriginalPortEven_of_globalPortChainEven G b y hy

/--
[kwDartPortSplit_weightedEnumerator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kwDartPortSplit_weightedEnumerator_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {W : KWDartEdgeBits G → ℂ} :
-- imply
  (∑ b : KWOriginalEvenBits G, W b.1) = ∑ p : KWSplitEvenBits G, W p.1.1 := by
-- proof
  apply StatMech.FrontierA.kwDartPortSplit_weightedEnumerator_eq G W

/--
[kw_det_portSplit_of_effective_gauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean)
-/
@[path]
private lemma kw_det_portSplit_of_effective_gauge_eq
  [Fintype External]
  [DecidableEq External]
  [Fintype Internal]
  [DecidableEq Internal]
  {original external : Matrix External External ℂ}
  {enter : Matrix External Internal ℂ}
  {exit : Matrix Internal External ℂ}
  {internal : Matrix Internal Internal ℂ}
  {nilpotenceIndex : ℕ}
  {gauge : External → ℂ}
-- given
  (hpow : internal ^ nilpotenceIndex = 0)
  (hgauge : ∀ i, gauge i ≠ 0)
  (heffective : kwEliminateAcyclicInternal external enter exit internal nilpotenceIndex = kwGaugeConjugate gauge original) :
-- imply
  (1 - kwInternalGadgetTransition external enter exit internal).det = (1 - original).det := by
-- proof
  apply StatMech.FrontierA.kw_det_portSplit_of_effective_gauge original external enter exit internal nilpotenceIndex hpow gauge hgauge heffective


-- created on 2026-10-23
