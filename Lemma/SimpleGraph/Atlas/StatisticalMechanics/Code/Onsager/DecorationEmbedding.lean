import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part11
open StatMech StatMech.Onsager


/--
[ons_decEmbedOffset_fst_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedOffset_fst_le_eq
  {mu : Fin 4} :
-- imply
  (ons_decEmbedOffset mu).1 ≤ 6 := by
-- proof
  apply StatMech.Onsager.ons_decEmbedOffset_fst_le mu

/--
[ons_decEmbedOffset_snd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedOffset_snd_le_eq
  {mu : Fin 4} :
-- imply
  (ons_decEmbedOffset mu).2 ≤ 6 := by
-- proof
  apply StatMech.Onsager.ons_decEmbedOffset_snd_le mu

/--
[ons_decEmbedCoord_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedCoord_lt_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : ZMod L}
  {c : ℕ}
-- given
  (hc : c ≤ 6) :
-- imply
  8 * z.val + c < 8 * L := by
-- proof
  apply StatMech.Onsager.ons_decEmbedCoord_lt L z c hc

/--
[ons_decEmbedVertex_fst_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedVertex_fst_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  (ons_decEmbedVertex L d).1.val = 8 * d.1.1.val + (ons_decEmbedOffset d.2).1 := by
-- proof
  apply StatMech.Onsager.ons_decEmbedVertex_fst_val L d

/--
[ons_decEmbedVertex_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedVertex_snd_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  (ons_decEmbedVertex L d).2.val = 8 * d.1.2.val + (ons_decEmbedOffset d.2).2 := by
-- proof
  apply StatMech.Onsager.ons_decEmbedVertex_snd_val L d

/--
[ons_decEmbedVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedVertex_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (ons_decEmbedVertex L) := by
-- proof
  apply StatMech.Onsager.ons_decEmbedVertex_injective L

/--
[ons_eight_zmodCast_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_eight_zmodCast_add_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  (8 : ZMod (8 * L)) * ZMod.cast z + 8 = 8 * ZMod.cast (z + 1) := by
-- proof
  apply StatMech.Onsager.ons_eight_zmodCast_add_one L z

/--
[ons_eight_zmodCast_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_eight_zmodCast_sub_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  (8 : ZMod (8 * L)) * ZMod.cast z - 8 = 8 * ZMod.cast (z - 1) := by
-- proof
  apply StatMech.Onsager.ons_eight_zmodCast_sub_one L z

/--
[ons_decEdgeRoute_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRoute_endpoint_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  ons_fourDirSteps (8 * L) (ons_decEdgeRouteDirs L d e) (ons_decEmbedVertex L d) = ons_decEmbedVertex L e := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRoute_endpoint L d e hde

/--
[ons_torusAdj_dirStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_torusAdj_dirStep_eq
  {N : ℕ}
  [Fact (2 < N)]
  {p : ZMod N × ZMod N}
  {mu : Fin 4} :
-- imply
  (onsTorusGraph N).Adj p (ons_dirStep N mu p) := by
-- proof
  apply StatMech.Onsager.ons_torusAdj_dirStep N p mu

/--
[ons_fourDirStepWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_fourDirStepWalk_length_eq
  {N : ℕ}
  [Fact (2 < N)]
  {r : Fin 4 → Fin 4}
  {p : ZMod N × ZMod N} :
-- imply
  (ons_fourDirStepWalk N r p).length = 4 := by
-- proof
  apply StatMech.Onsager.ons_fourDirStepWalk_length N r p

/--
[ons_decEdgeRoute_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRoute_length_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  (ons_decEdgeRoute L d e hde).length = 4 := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRoute_length L d e hde

/--
[ons_decEdgeRoute_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRoute_support_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  (ons_decEdgeRoute L d e hde).support = ons_decEdgeRouteVertices L d e := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRoute_support L d e hde

/--
[ons_decEdgeRouteVertices_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRouteVertices_length_eq
  {L : ℕ}
  {d e : ons_Dart L} :
-- imply
  (ons_decEdgeRouteVertices L d e).length = 5 := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRouteVertices_length L d e

/--
[ons_decEmbed_smallIntCast_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbed_smallIntCast_eq_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : ℤ}
-- given
  (ha₀ : -4 ≤ a)
  (ha₁ : a ≤ 12)
  (hb₀ : -4 ≤ b)
  (hb₁ : b ≤ 12) :
-- imply
  (a : ZMod (8 * L)) = (b : ZMod (8 * L)) ↔ a = b := by
-- proof
  apply StatMech.Onsager.ons_decEmbed_smallIntCast_eq_iff L ha₀ ha₁ hb₀ hb₁

/--
[ons_decEdgeRoute_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRoute_isPath_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  (ons_decEdgeRoute L d e hde).IsPath := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRoute_isPath L d e hde

/--
[ons_decMicroVertex_fst_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decMicroVertex_fst_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : ons_DecMicroPoint L} :
-- imply
  (ons_decMicroVertex L z).1.val = 8 * z.cell.1.val + z.offsetX.val := by
-- proof
  apply StatMech.Onsager.ons_decMicroVertex_fst_val L z

/--
[ons_decMicroVertex_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decMicroVertex_snd_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : ons_DecMicroPoint L} :
-- imply
  (ons_decMicroVertex L z).2.val = 8 * z.cell.2.val + z.offsetY.val := by
-- proof
  apply StatMech.Onsager.ons_decMicroVertex_snd_val L z

/--
[ons_decMicroVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decMicroVertex_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (ons_decMicroVertex L) := by
-- proof
  apply StatMech.Onsager.ons_decMicroVertex_injective L

/--
[ons_decInternalRoute_interior_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decInternalRoute_interior_support_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hint : ons_decInternalAdj d e) :
-- imply
  (ons_decEdgeRouteVertices L d e).tail.dropLast = (ons_decEdgeInteriorData L d e).map (ons_decMicroVertex L) := by
-- proof
  apply StatMech.Onsager.ons_decInternalRoute_interior_support L d e hint

/--
[ons_decMicroCorridorEdge_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decMicroCorridorEdge_of_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
  {z : ons_DecMicroPoint L}
-- given
  (hde : (ons_decGraph L).Adj d e)
  (hz : z ∈ ons_decEdgeInteriorData L d e) :
-- imply
  ons_decMicroCorridorEdge L z = s(d, e) := by
-- proof
  apply StatMech.Onsager.ons_decMicroCorridorEdge_of_mem L d e hde hz

/--
[ons_decEdgeRoute_interior_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRoute_interior_support_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  (ons_decEdgeRoute L d e hde).support.tail.dropLast = (ons_decEdgeInteriorData L d e).map (ons_decMicroVertex L) := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRoute_interior_support L d e hde

/--
[ons_decEdgeRoute_edge_eq_of_interior_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRoute_edge_eq_of_interior_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e f g : ons_Dart L}
  {x : ZMod (8 * L) × ZMod (8 * L)}
-- given
  (hde : (ons_decGraph L).Adj d e)
  (hfg : (ons_decGraph L).Adj f g)
  (hx : x ∈ (ons_decEdgeRoute L d e hde).support.tail.dropLast)
  (hy : x ∈ (ons_decEdgeRoute L f g hfg).support.tail.dropLast) :
-- imply
  s(d, e) = s(f, g) := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRoute_edge_eq_of_interior_mem L d e f g hde hfg hx hy

/--
[ons_decEdgeInteriorData_offset_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeInteriorData_offset_mem_eq
  {L : ℕ}
  {d e : ons_Dart L}
  {z : ons_DecMicroPoint L}
-- given
  (hz : z ∈ ons_decEdgeInteriorData L d e) :
-- imply
  (z.offsetX, z.offsetY) ∈ ons_decInteriorOffsets := by
-- proof
  apply StatMech.Onsager.ons_decEdgeInteriorData_offset_mem L d e hz

/--
[ons_decMicroVertex_port](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decMicroVertex_port_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  ons_decMicroVertex L (ons_decPortMicroPoint L d) = ons_decEmbedVertex L d := by
-- proof
  apply StatMech.Onsager.ons_decMicroVertex_port L d

/--
[ons_decPort_offset_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decPort_offset_not_mem_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  ((ons_decPortMicroPoint L d).offsetX, (ons_decPortMicroPoint L d).offsetY) ∉ ons_decInteriorOffsets := by
-- proof
  apply StatMech.Onsager.ons_decPort_offset_not_mem L d

/--
[ons_decEmbedVertex_not_mem_route_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedVertex_not_mem_route_interior_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d f g : ons_Dart L}
-- given
  (hfg : (ons_decGraph L).Adj f g) :
-- imply
  ons_decEmbedVertex L d ∉ (ons_decEdgeRoute L f g hfg).support.tail.dropLast := by
-- proof
  apply StatMech.Onsager.ons_decEmbedVertex_not_mem_route_interior L d f g hfg

/--
[ons_decEdgeRoute_tail_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEdgeRoute_tail_support_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
-- given
  (hde : (ons_decGraph L).Adj d e) :
-- imply
  (ons_decEdgeRoute L d e hde).support.tail = (ons_decEdgeRoute L d e hde).support.tail.dropLast ++ [ons_decEmbedVertex L e] := by
-- proof
  apply StatMech.Onsager.ons_decEdgeRoute_tail_support L d e hde

/--
[ons_mem_decDartSegment_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_mem_decDartSegment_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a : (ons_decGraph L).Dart}
  {x : ZMod (8 * L) × ZMod (8 * L)} :
-- imply
  x ∈ ons_decDartSegment L a ↔ x ∈ (ons_decEdgeRoute L a.fst a.snd a.adj).support.tail.dropLast ∨ x = ons_decEmbedVertex L a.snd := by
-- proof
  apply StatMech.Onsager.ons_mem_decDartSegment_iff L a x

/--
[ons_decDartSegment_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decDartSegment_nodup_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a : (ons_decGraph L).Dart} :
-- imply
  (ons_decDartSegment L a).Nodup := by
-- proof
  apply StatMech.Onsager.ons_decDartSegment_nodup L a

/--
[ons_decDartSegment_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decDartSegment_disjoint_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : (ons_decGraph L).Dart}
-- given
  (hedge : a.edge ≠ b.edge)
  (hsnd : a.snd ≠ b.snd) :
-- imply
  List.Disjoint (ons_decDartSegment L a) (ons_decDartSegment L b) := by
-- proof
  apply StatMech.Onsager.ons_decDartSegment_disjoint L a b hedge hsnd

/--
[ons_decEmbedWalk_tail_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedWalk_tail_support_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  (ons_decEmbedWalk L p).support.tail = p.darts.flatMap (ons_decDartSegment L) := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_tail_support L p

/--
[ons_decEmbedWalk_length_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedWalk_length_aux_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  (ons_decEmbedWalk L p).length = 4 * p.length := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_length_aux L p

/--
[ons_decEmbedWalk_tail_nodup_of_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedWalk_tail_nodup_of_isCycle_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {p : (ons_decGraph L).Walk d d}
-- given
  (hp : p.IsCycle) :
-- imply
  (ons_decEmbedWalk L p).support.tail.Nodup := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_tail_nodup_of_isCycle L p hp

/--
[ons_decEmbedWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedWalk_isCycle_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {p : (ons_decGraph L).Walk d d}
-- given
  (hp : p.IsCycle) :
-- imply
  (ons_decEmbedWalk L p).IsCycle := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_isCycle L p hp

/--
[ons_decEmbedWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean)
-/
@[path]
private lemma ons_decEmbedWalk_length_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  (ons_decEmbedWalk L p).length = 4 * p.length := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_length L p


-- created on 2026-10-23
