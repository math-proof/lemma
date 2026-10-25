import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
open StatMech StatMech.Onsager


/--
[ons_pathDisplacement_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_nil_eq :
-- imply
  ons_pathDisplacement [] = 0 := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_nil

/--
[ons_pathDisplacement_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_cons_eq
  {d : Fin 4}
  {ds : List (Fin 4)} :
-- imply
  ons_pathDisplacement (d :: ds) = stepOf d + ons_pathDisplacement ds := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_cons d ds

/--
[ons_pathVertices_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_nil_eq :
-- imply
  ons_pathVertices [] = [0] := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_nil

/--
[ons_pathVertices_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_cons_eq
  {d : Fin 4}
  {ds : List (Fin 4)} :
-- imply
  ons_pathVertices (d :: ds) = 0 :: (ons_pathVertices ds).map (stepOf d + ·) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_cons d ds

/--
[ons_pathDisplacement_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_append_eq
  {l r : List (Fin 4)} :
-- imply
  ons_pathDisplacement (l ++ r) = ons_pathDisplacement l + ons_pathDisplacement r := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_append l r

/--
[ons_pathVertices_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_length_eq
  {l : List (Fin 4)} :
-- imply
  (ons_pathVertices l).length = l.length + 1 := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_length l

/--
[ons_pathVertices_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_head_eq
  {l : List (Fin 4)} :
-- imply
  (ons_pathVertices l).head? = some 0 := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_head l

/--
[ons_pathVertices_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_getLast_eq
  {l : List (Fin 4)} :
-- imply
  (ons_pathVertices l).getLast? = some (ons_pathDisplacement l) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_getLast l

/--
[ons_pathVertices_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_append_eq
  {l r : List (Fin 4)} :
-- imply
  ons_pathVertices (l ++ r) = (ons_pathVertices l).dropLast ++ (ons_pathVertices r).map (ons_pathDisplacement l + ·) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_append l r

/--
[ons_pathVertices_append_dropLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_append_dropLast_eq
  {l r : List (Fin 4)} :
-- imply
  (ons_pathVertices (l ++ r)).dropLast = (ons_pathVertices l).dropLast ++ (ons_pathVertices r).dropLast.map (ons_pathDisplacement l + ·) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_append_dropLast l r

/--
[ons_mem_pathVertices_append_dropLast_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_mem_pathVertices_append_dropLast_iff_eq
  {l r : List (Fin 4)}
  {z : ℤ × ℤ} :
-- imply
  z ∈ (ons_pathVertices (l ++ r)).dropLast ↔ z ∈ (ons_pathVertices l).dropLast ∨ ∃ w ∈ (ons_pathVertices r).dropLast, z = ons_pathDisplacement l + w := by
-- proof
  apply StatMech.Onsager.ons_mem_pathVertices_append_dropLast_iff l r z

/--
[ons_openTurnSum_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_nil_eq :
-- imply
  ons_openTurnSum [] = 0 := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_nil

/--
[ons_openTurnSum_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_singleton_eq
  {d : Fin 4} :
-- imply
  ons_openTurnSum [d] = 0 := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_singleton d

/--
[ons_openTurnSum_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_cons_cons_eq
  {d e : Fin 4}
  {ds : List (Fin 4)} :
-- imply
  ons_openTurnSum (d :: e :: ds) = ons_turnPow d e + ons_openTurnSum (e :: ds) := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_cons_cons d e ds

/--
[ons_openTurnSum_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_append_eq
  {l r : List (Fin 4)}
-- given
  (hl : l ≠ [])
  (hr : r ≠ []) :
-- imply
  ons_openTurnSum (l ++ r) = ons_openTurnSum l + ons_turnPow l.getLast! r.head! + ons_openTurnSum r := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_append l r hl hr

/--
[ons_openTurnSum_replicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_replicate_eq
  {n : ℕ}
  {d : Fin 4} :
-- imply
  ons_openTurnSum (List.replicate n d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_replicate n d

/--
[ons_getLast_replicate_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_getLast_replicate_succ_eq
  {n : ℕ}
  {d : Fin 4} :
-- imply
  (List.replicate (n + 1) d).getLast! = d := by
-- proof
  apply StatMech.Onsager.ons_getLast_replicate_succ n d

/--
[ons_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_getLast_eq
  {n : ℕ}
  {d : Fin 4} :
-- imply
  (List.replicate (n + 1) d).getLast?.getD 0 = d := by
-- proof
  apply StatMech.Onsager.ons_getLast n d

/--
[ons_head_replicate_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_head_replicate_succ_eq
  {n : ℕ}
  {d : Fin 4} :
-- imply
  (List.replicate (n + 1) d).head! = d := by
-- proof
  apply StatMech.Onsager.ons_head_replicate_succ n d

/--
[ons_pathDisplacement_replicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_replicate_eq
  {n : ℕ}
  {d : Fin 4} :
-- imply
  ons_pathDisplacement (List.replicate n d) = n • stepOf d := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_replicate n d

/--
[ons_pathVertices_replicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_replicate_eq
  {n : ℕ}
  {d : Fin 4} :
-- imply
  ons_pathVertices (List.replicate n d) = (List.range (n + 1)).map (fun k ↦ k • stepOf d) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_replicate n d

/--
[ons_mem_pathVertices_replicate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_mem_pathVertices_replicate_iff_eq
  {n : ℕ}
  {d : Fin 4}
  {z : ℤ × ℤ} :
-- imply
  z ∈ ons_pathVertices (List.replicate n d) ↔ ∃ k : ℕ, k ≤ n ∧ z = k • stepOf d := by
-- proof
  apply StatMech.Onsager.ons_mem_pathVertices_replicate_iff n d z

/--
[ons_pathVertices_replicate_dropLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_replicate_dropLast_eq
  {n : ℕ}
  {d : Fin 4} :
-- imply
  (ons_pathVertices (List.replicate n d)).dropLast = (List.range n).map (fun k ↦ k • stepOf d) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_replicate_dropLast n d

/--
[ons_map_pathVertices_replicate_dropLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_map_pathVertices_replicate_dropLast_eq
  {f : (ℤ × ℤ) → X}
  {n : ℕ}
  {d : Fin 4} :
-- imply
  (List.map f (ons_pathVertices (List.replicate n d))).dropLast = (List.range n).map (fun k ↦ f (k • stepOf d)) := by
-- proof
  apply StatMech.Onsager.ons_map_pathVertices_replicate_dropLast f n d

/--
[ons_mem_pathVertices_replicate_dropLast_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_mem_pathVertices_replicate_dropLast_iff_eq
  {n : ℕ}
  {d : Fin 4}
  {z : ℤ × ℤ} :
-- imply
  z ∈ (ons_pathVertices (List.replicate n d)).dropLast ↔ ∃ k : ℕ, k < n ∧ z = k • stepOf d := by
-- proof
  apply StatMech.Onsager.ons_mem_pathVertices_replicate_dropLast_iff n d z

/--
[ons_outsideConnector_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_ne_nil_eq
  {dx dy top : ℤ} :
-- imply
  ons_outsideConnector dx dy top ≠ [] := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_ne_nil dx dy top

/--
[ons_outsideConnector_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_head_eq
  {dx dy top : ℤ} :
-- imply
  (ons_outsideConnector dx dy top).head! = 0 := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_head dx dy top

/--
[ons_outsideConnector_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_getLast_eq
  {dx dy top : ℤ} :
-- imply
  (ons_outsideConnector dx dy top).getLast! = 0 := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_getLast dx dy top

/--
[ons_outsideConnector_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_displacement_eq
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  ons_pathDisplacement (ons_outsideConnector dx dy top) = (-dx, -dy) := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_displacement dx dy top hdx hdy htop

/--
[ons_openTurnSum_five_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_five_blocks_eq
  {a b c d e : Fin 4}
  {na nb nc nd ne : ℕ} :
-- imply
  ons_openTurnSum (List.replicate (na + 1) a ++ List.replicate (nb + 1) b ++ List.replicate (nc + 1) c ++ List.replicate (nd + 1) d ++ List.replicate (ne + 1) e) = ons_turnPow a b + ons_turnPow b c + ons_turnPow c d + ons_turnPow d e := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_five_blocks a b c d e na nb nc nd ne

/--
[ons_outsideConnector_openTurnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_openTurnSum_eq
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  ons_openTurnSum (ons_outsideConnector dx dy top) = 4 := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_openTurnSum dx dy top hdx hdy htop

/--
[ons_mem_outsideConnector_vertices_dropLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_mem_outsideConnector_vertices_dropLast_eq
  {dx dy top : ℤ}
  {z : ℤ × ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top)
  (hz : z ∈ (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast) :
-- imply
  z = 0 ∨ (∃ k : ℕ, k < (top - dy).toNat ∧ z = (1, (k : ℤ))) ∨ (∃ k : ℕ, k < (dx + 2).toNat ∧ z = (1 - (k : ℤ), top - dy)) ∨ (∃ k : ℕ, k < top.toNat ∧ z = (-dx - 1, top - dy - (k : ℤ))) ∨ z = (-dx - 1, -dy) := by
-- proof
  apply StatMech.Onsager.ons_mem_outsideConnector_vertices_dropLast dx dy top hdx hdy htop z hz

/--
[ons_outsideConnector_vertices_dropLast_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_vertices_dropLast_eq_eq
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast = ons_outsideConnectorVertexList dx dy top := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_vertices_dropLast_eq dx dy top hdx hdy htop

/--
[ons_outsideConnectorVertexList_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnectorVertexList_nodup_eq
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  (ons_outsideConnectorVertexList dx dy top).Nodup := by
-- proof
  apply StatMech.Onsager.ons_outsideConnectorVertexList_nodup dx dy top hdx hdy htop

/--
[ons_outsideConnector_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_vertices_dropLast_nodup_eq
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast.Nodup := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_vertices_dropLast_nodup dx dy top hdx hdy htop

/--
[ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup_eq
  {l : List (Fin 4)}
-- given
  (hnodup : (ons_pathVertices l).Nodup) :
-- imply
  ons_pathDisplacement l ∉ (ons_pathVertices l).dropLast := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup l hnodup

/--
[ons_outsideConnector_shift_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_outsideConnector_shift_disjoint_eq
  {l : List (Fin 4)}
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top)
  (hdisp : ons_pathDisplacement l = (dx, dy))
  (hnodup : (ons_pathVertices l).Nodup)
  (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
  (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
  (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
-- imply
  ∀ z ∈ (ons_pathVertices l).dropLast, ∀ w ∈ (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast, z ≠ ons_pathDisplacement l + w := by
-- proof
  apply StatMech.Onsager.ons_outsideConnector_shift_disjoint l dx dy top hdx hdy htop hdisp hnodup hxmin hxmax hymax

/--
[ons_boundingClosure_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_boundingClosure_vertices_dropLast_nodup_eq
  {l : List (Fin 4)}
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top)
  (hdisp : ons_pathDisplacement l = (dx, dy))
  (hnodup : (ons_pathVertices l).Nodup)
  (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
  (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
  (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
-- imply
  (ons_pathVertices (l ++ ons_outsideConnector dx dy top)).dropLast.Nodup := by
-- proof
  apply StatMech.Onsager.ons_boundingClosure_vertices_dropLast_nodup l dx dy top hdx hdy htop hdisp hnodup hxmin hxmax hymax

/--
[ons_pos_succ_eq_head_add_pos_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pos_succ_eq_head_add_pos_tail_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin (n + 1) → Fin 4}
  {i : Fin n} :
-- imply
  pos d i.succ = stepOf (d 0) + pos (fun j : Fin n ↦ d j.succ) i := by
-- proof
  apply StatMech.Onsager.ons_pos_succ_eq_head_add_pos_tail d i

/--
[ons_pathVertices_dropLast_eq_ofFn_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_dropLast_eq_ofFn_pos_eq
  {l : List (Fin 4)}
  [NeZero l.length] :
-- imply
  (ons_pathVertices l).dropLast = List.ofFn (pos (fun i : Fin l.length ↦ l.get i)) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_dropLast_eq_ofFn_pos l

/--
[ons_pos_get_injective_of_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pos_get_injective_of_vertices_dropLast_nodup_eq
  {l : List (Fin 4)}
  [NeZero l.length]
-- given
  (hnodup : (ons_pathVertices l).dropLast.Nodup) :
-- imply
  Function.Injective (pos (fun i : Fin l.length ↦ l.get i)) := by
-- proof
  apply StatMech.Onsager.ons_pos_get_injective_of_vertices_dropLast_nodup l hnodup

/--
[ons_pathDisplacement_eq_sum_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_eq_sum_map_eq
  {l : List (Fin 4)} :
-- imply
  ons_pathDisplacement l = (l.map stepOf).sum := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_eq_sum_map l

/--
[ons_pathDisplacement_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_ofFn_eq
  {n : ℕ}
  {d : Fin n → Fin 4} :
-- imply
  ons_pathDisplacement (List.ofFn d) = ∑ i, stepOf (d i) := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_ofFn d

/--
[ons_openTurnSum_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_ofFn_eq
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4} :
-- imply
  ons_openTurnSum (List.ofFn d) = ∑ i : Fin n, ons_turnPow (d i.castSucc) (d i.succ) := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_ofFn d

/--
[ons_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_getLast_eq_2
  [Inhabited X]
  {n : ℕ}
  {f : Fin (n + 1) → X} :
-- imply
  (List.ofFn f).getLast! = f (Fin.last n) := by
-- proof
  apply StatMech.Onsager.ons_getLast f

/--
[ons_cyclicTurnSum_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_cyclicTurnSum_ofFn_eq
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4} :
-- imply
  ons_cyclicTurnSum (List.ofFn d) = ∑ i, ons_turnPow (d i) (d (i + 1)) := by
-- proof
  apply StatMech.Onsager.ons_cyclicTurnSum_ofFn d

/--
[ons_cyclicTurnSum_ofFn'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_cyclicTurnSum_ofFn'_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4} :
-- imply
  ons_cyclicTurnSum (List.ofFn d) = ∑ i, ons_turnPow (d i) (d (i + 1)) := by
-- proof
  apply StatMech.Onsager.ons_cyclicTurnSum_ofFn' d

/--
[ons_cyclicTurnSum_eq_four_or_neg_four_of_list](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_cyclicTurnSum_eq_four_or_neg_four_of_list_eq
  {l : List (Fin 4)}
  [NeZero l.length]
-- given
  (hclosed : ons_pathDisplacement l = 0)
  (hsimple : (ons_pathVertices l).dropLast.Nodup)
  (hlen : 3 ≤ l.length)
  (hnu : ∀ i : Fin l.length, l.get (i + 1) ≠ l.get i + 2) :
-- imply
  ons_cyclicTurnSum l = 4 ∨ ons_cyclicTurnSum l = -4 := by
-- proof
  apply StatMech.Onsager.ons_cyclicTurnSum_eq_four_or_neg_four_of_list l hclosed hsimple hlen hnu

/--
[ons_stepOf_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_stepOf_add_two_eq
  {w : Fin 4} :
-- imply
  stepOf (w + 2) = -stepOf w := by
-- proof
  apply StatMech.Onsager.ons_stepOf_add_two w

/--
[ons_nonUturn_of_pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_nonUturn_of_pos_injective_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hinj : Function.Injective (pos d))
  (hn : 3 ≤ n) :
-- imply
  ∀ i, d (i + 1) ≠ d i + 2 := by
-- proof
  apply StatMech.Onsager.ons_nonUturn_of_pos_injective d hclosed hinj hn

/--
[ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list_eq
  {l : List (Fin 4)}
  [NeZero l.length]
-- given
  (hclosed : ons_pathDisplacement l = 0)
  (hsimple : (ons_pathVertices l).dropLast.Nodup)
  (hlen : 3 ≤ l.length) :
-- imply
  ons_cyclicTurnSum l = 4 ∨ ons_cyclicTurnSum l = -4 := by
-- proof
  apply StatMech.Onsager.ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list l hclosed hsimple hlen

/--
[ons_boundingClosure_turnSum_eq_four_or_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_boundingClosure_turnSum_eq_four_or_neg_four_eq
  {l : List (Fin 4)}
  {dx dy top : ℤ}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top)
  (hdisp : ons_pathDisplacement l = (dx, dy))
  (hnodup : (ons_pathVertices l).Nodup)
  (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
  (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
  (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
-- imply
  ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) = 4 ∨ ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) = -4 := by
-- proof
  apply StatMech.Onsager.ons_boundingClosure_turnSum_eq_four_or_neg_four l dx dy top hdx hdy htop hdisp hnodup hxmin hxmax hymax

/--
[ons_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_getLast_eq_3
  [Inhabited X]
  {l : List X}
-- given
  (h : l ≠ []) :
-- imply
  l.getLast! = l.getLast h := by
-- proof
  apply StatMech.Onsager.ons_getLast l h

/--
[ons_boundingClosure_cyclicTurnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_boundingClosure_cyclicTurnSum_eq
  {l : List (Fin 4)}
  {dx dy top : ℤ}
-- given
  (hl : l ≠ [])
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) = ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 + ons_turnPow 0 l.head! := by
-- proof
  apply StatMech.Onsager.ons_boundingClosure_cyclicTurnSum l hl dx dy top hdx hdy htop

/--
[ons_three_values_force_step_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_three_values_force_step_zero_eq
  {a t : ℤ}
-- given
  (h0 : a = 4 ∨ a = -4)
  (h1 : a + t = 4 ∨ a + t = -4)
  (h2 : a + 2 * t = 4 ∨ a + 2 * t = -4) :
-- imply
  t = 0 := by
-- proof
  apply StatMech.Onsager.ons_three_values_force_step_zero a t h0 h1 h2

/--
[ons_periodStateList_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodStateList_nodup_eq
  {n r : ℕ} :
-- imply
  (ons_periodStateList n r).Nodup := by
-- proof
  apply StatMech.Onsager.ons_periodStateList_nodup n r

/--
[ons_mem_allPeriodStates_fst_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_mem_allPeriodStates_fst_le_eq
  {n N : ℕ}
  {z : ℕ × Fin n}
-- given
  (hz : z ∈ ons_allPeriodStates n N) :
-- imply
  z.1 ≤ N := by
-- proof
  apply StatMech.Onsager.ons_mem_allPeriodStates_fst_le n N z hz

/--
[ons_allPeriodStates_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_allPeriodStates_nodup_eq
  {n N : ℕ} :
-- imply
  (ons_allPeriodStates n N).Nodup := by
-- proof
  apply StatMech.Onsager.ons_allPeriodStates_nodup n N

/--
[ons_periodStateList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodStateList_length_eq
  {n r : ℕ} :
-- imply
  (ons_periodStateList n r).length = n := by
-- proof
  apply StatMech.Onsager.ons_periodStateList_length n r

/--
[ons_allPeriodStates_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_allPeriodStates_length_eq
  {n N : ℕ} :
-- imply
  (ons_allPeriodStates n N).length = (N + 1) * n := by
-- proof
  apply StatMech.Onsager.ons_allPeriodStates_length n N

/--
[ons_periodicArcStates_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArcStates_nodup_eq
  {n : ℕ}
  {N : ℕ}
  {imin imax : Fin n} :
-- imply
  (ons_periodicArcStates N imin imax).Nodup := by
-- proof
  apply StatMech.Onsager.ons_periodicArcStates_nodup N imin imax

/--
[ons_periodicArcStates_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArcStates_length_eq
  {n : ℕ}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  (ons_periodicArcStates N imin imax).length = N * n + imax.val + 1 - imin.val := by
-- proof
  apply StatMech.Onsager.ons_periodicArcStates_length N hN imin imax

/--
[ons_mem_periodicArcStates_fst_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_mem_periodicArcStates_fst_le_eq
  {n : ℕ}
  {N : ℕ}
  {imin imax : Fin n}
  {z : ℕ × Fin n}
-- given
  (hz : z ∈ ons_periodicArcStates N imin imax) :
-- imply
  z.1 ≤ N := by
-- proof
  apply StatMech.Onsager.ons_mem_periodicArcStates_fst_le N imin imax z hz

/--
[ons_periodStateList_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodStateList_isChain_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {r : ℕ} :
-- imply
  List.IsChain (fun a b ↦ ons_periodStateCoord d b = ons_periodStateCoord d a + stepOf (d a.2)) (ons_periodStateList n r) := by
-- proof
  apply StatMech.Onsager.ons_periodStateList_isChain d r

/--
[ons_periodState_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodState_boundary_eq
  {m : ℕ}
  {d : Fin (m + 1) → Fin 4}
  {r : ℕ} :
-- imply
  ons_periodStateCoord d (r + 1, 0) = ons_periodStateCoord d (r, Fin.last m) + stepOf (d (Fin.last m)) := by
-- proof
  apply StatMech.Onsager.ons_periodState_boundary d r

/--
[ons_periodStateList_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodStateList_head_eq
  {n : ℕ}
  [NeZero n]
  {r : ℕ} :
-- imply
  (ons_periodStateList n r).head? = some (r, (0 : Fin n)) := by
-- proof
  apply StatMech.Onsager.ons_periodStateList_head r

/--
[ons_periodStateList_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodStateList_getLast_eq
  {n : ℕ}
  [NeZero n]
  {r : ℕ} :
-- imply
  (ons_periodStateList n r).getLast? = some (r, ons_lastFin n) := by
-- proof
  apply StatMech.Onsager.ons_periodStateList_getLast r

/--
[ons_allPeriodStates_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_allPeriodStates_getLast_eq
  {n : ℕ}
  [NeZero n]
  {N : ℕ} :
-- imply
  (ons_allPeriodStates n N).getLast? = some (N, ons_lastFin n) := by
-- proof
  apply StatMech.Onsager.ons_allPeriodStates_getLast N

/--
[ons_allPeriodStates_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_allPeriodStates_isChain_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ} :
-- imply
  List.IsChain (fun a b ↦ ons_periodStateCoord d b = ons_periodStateCoord d a + stepOf (d a.2)) (ons_allPeriodStates n N) := by
-- proof
  apply StatMech.Onsager.ons_allPeriodStates_isChain d N

/--
[ons_periodicArcStates_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArcStates_isChain_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n} :
-- imply
  List.IsChain (fun a b ↦ ons_periodStateCoord d b = ons_periodStateCoord d a + stepOf (d a.2)) (ons_periodicArcStates N imin imax) := by
-- proof
  apply StatMech.Onsager.ons_periodicArcStates_isChain d N imin imax

/--
[ons_periodicArcStates_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArcStates_head_eq
  {n : ℕ}
  [NeZero n]
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  (ons_periodicArcStates N imin imax).head? = some (0, imin) := by
-- proof
  apply StatMech.Onsager.ons_periodicArcStates_head N hN imin imax

/--
[ons_periodicArcStates_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArcStates_getLast_eq
  {n : ℕ}
  [NeZero n]
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  (ons_periodicArcStates N imin imax).getLast? = some (N, imax) := by
-- proof
  apply StatMech.Onsager.ons_periodicArcStates_getLast N hN imin imax

/--
[ons_pathVertices_map_dropLast_of_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathVertices_map_dropLast_of_chain_eq
  [Inhabited X]
  {coord : X → ℤ × ℤ}
  {dir : X → Fin 4}
  {s : List X}
-- given
  (hs : s ≠ [])
  (hchain : List.IsChain (fun a b ↦ coord b = coord a + stepOf (dir a)) s) :
-- imply
  ons_pathVertices (s.dropLast.map dir) = s.map (fun x ↦ coord x - coord s.head!) := by
-- proof
  apply StatMech.Onsager.ons_pathVertices_map_dropLast_of_chain coord dir s hs hchain

/--
[ons_periodicArc_pathVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArc_pathVertices_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  ons_pathVertices (ons_periodicArcDirections d N imin imax) = (ons_periodicArcStates N imin imax).map (fun z ↦ ons_periodStateCoord d z - ons_periodStateCoord d (0, imin)) := by
-- proof
  apply StatMech.Onsager.ons_periodicArc_pathVertices d N hN imin imax

/--
[ons_periodicArc_pathVertices_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArc_pathVertices_nodup_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N)
  (hinj : Function.Injective (ons_periodStateCoord d)) :
-- imply
  (ons_pathVertices (ons_periodicArcDirections d N imin imax)).Nodup := by
-- proof
  apply StatMech.Onsager.ons_periodicArc_pathVertices_nodup d N hN imin imax hinj

/--
[ons_periodicArc_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArc_displacement_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  ons_pathDisplacement (ons_periodicArcDirections d N imin imax) = ons_periodStateCoord d (N, imax) - ons_periodStateCoord d (0, imin) := by
-- proof
  apply StatMech.Onsager.ons_periodicArc_displacement d N hN imin imax

/--
[ons_periodicArc_xmin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArc_xmin_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N)
  (hmin : ∀ i, (pos d imin).1 ≤ (pos d i).1)
  (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
-- imply
  ∀ z ∈ (ons_pathVertices (ons_periodicArcDirections d N imin imax)).dropLast, 0 ≤ z.1 := by
-- proof
  apply StatMech.Onsager.ons_periodicArc_xmin d N hN imin imax hmin hD

/--
[ons_periodicArc_xmax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArc_xmax_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N)
  (hmax : ∀ i, (pos d i).1 ≤ (pos d imax).1)
  (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
-- imply
  ∀ z ∈ (ons_pathVertices (ons_periodicArcDirections d N imin imax)).dropLast, z.1 ≤ (ons_periodStateCoord d (N, imax) - ons_periodStateCoord d (0, imin)).1 := by
-- proof
  apply StatMech.Onsager.ons_periodicArc_xmax d N hN imin imax hmax hD

/--
[ons_exists_path_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_exists_path_top_eq
  {l : List (Fin 4)}
  {dy : ℤ} :
-- imply
  ∃ top : ℤ, 0 < top ∧ dy < top ∧ ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top := by
-- proof
  apply StatMech.Onsager.ons_exists_path_top l dy

/--
[ons_periodicArc_adjustedTurn_eq_four_or_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArc_adjustedTurn_eq_four_or_neg_four_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N)
  (hinj : Function.Injective (ons_periodStateCoord d))
  (hmin : ∀ i, (pos d imin).1 ≤ (pos d i).1)
  (hmax : ∀ i, (pos d i).1 ≤ (pos d imax).1)
  (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
-- imply
  let l := ons_periodicArcDirections d N imin imax ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 + ons_turnPow 0 l.head! = 4 ∨ ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 + ons_turnPow 0 l.head! = -4 := by
-- proof
  apply StatMech.Onsager.ons_periodicArc_adjustedTurn_eq_four_or_neg_four d N hN imin imax hinj hmin hmax hD

/--
[ons_allPeriodStates_map_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_allPeriodStates_map_direction_eq
  {n : ℕ}
  {d : Fin n → Fin 4}
  {N : ℕ} :
-- imply
  (ons_allPeriodStates n N).map (fun z ↦ d z.2) = ons_directionPeriods d (N + 1) := by
-- proof
  apply StatMech.Onsager.ons_allPeriodStates_map_direction d N

/--
[ons_dropLast_take_of_pos_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_dropLast_take_of_pos_le_eq
  {l : List X}
  {k : ℕ}
-- given
  (hk : 0 < k)
  (hle : k ≤ l.length) :
-- imply
  (l.take k).dropLast = l.take (k - 1) := by
-- proof
  apply StatMech.Onsager.ons_dropLast_take_of_pos_le l k hk hle

/--
[ons_periodicArcDirections_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArcDirections_eq_slice_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  ons_periodicArcDirections d N imin imax = ((ons_directionPeriods d (N + 1)).drop imin.val).take (N * n + imax.val - imin.val) := by
-- proof
  apply StatMech.Onsager.ons_periodicArcDirections_eq_slice d N hN imin imax

/--
[ons_directionPeriods_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_directionPeriods_length_eq
  {n : ℕ}
  {d : Fin n → Fin 4}
  {N : ℕ} :
-- imply
  (ons_directionPeriods d N).length = N * n := by
-- proof
  apply StatMech.Onsager.ons_directionPeriods_length d N

/--
[ons_directionPeriods_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_directionPeriods_succ_eq
  {n : ℕ}
  {d : Fin n → Fin 4}
  {N : ℕ} :
-- imply
  ons_directionPeriods d (N + 1) = ons_directionPeriods d N ++ List.ofFn d := by
-- proof
  apply StatMech.Onsager.ons_directionPeriods_succ d N

/--
[ons_directionPeriods_append_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_directionPeriods_append_comm_eq
  {n : ℕ}
  {d : Fin n → Fin 4}
  {N : ℕ} :
-- imply
  ons_directionPeriods d N ++ List.ofFn d = List.ofFn d ++ ons_directionPeriods d N := by
-- proof
  apply StatMech.Onsager.ons_directionPeriods_append_comm d N

/--
[ons_directionPeriods_succ_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_directionPeriods_succ_left_eq
  {n : ℕ}
  {d : Fin n → Fin 4}
  {N : ℕ} :
-- imply
  ons_directionPeriods d (N + 1) = List.ofFn d ++ ons_directionPeriods d N := by
-- proof
  apply StatMech.Onsager.ons_directionPeriods_succ_left d N

/--
[ons_periodicArcDirections_eq_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArcDirections_eq_blocks_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  ons_periodicArcDirections d N imin imax = (List.ofFn d).drop imin.val ++ ons_directionPeriods d (N - 1) ++ (List.ofFn d).take imax.val := by
-- proof
  apply StatMech.Onsager.ons_periodicArcDirections_eq_blocks d N hN imin imax

/--
[ons_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_getLast_eq_4
  [Inhabited X]
  {l r : List X}
-- given
  (hr : r ≠ []) :
-- imply
  (l ++ r).getLast! = r.getLast! := by
-- proof
  apply StatMech.Onsager.ons_getLast l r hr

/--
[ons_openTurnSum_insert_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_openTurnSum_insert_cycle_eq
  {A D P : List (Fin 4)}
-- given
  (hA : A ≠ [])
  (hD : D ≠ [])
  (hlast : A.getLast! = D.getLast!)
  (hhead : P ≠ [] → P.head! = D.head!) :
-- imply
  ons_openTurnSum (A ++ D ++ P) = ons_openTurnSum (A ++ P) + ons_cyclicTurnSum D := by
-- proof
  apply StatMech.Onsager.ons_openTurnSum_insert_cycle A D P hA hD hlast hhead

/--
[ons_adjustedTurn_insert_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_adjustedTurn_insert_cycle_eq
  {A D P : List (Fin 4)}
-- given
  (hA : A ≠ [])
  (hD : D ≠ [])
  (hlast : A.getLast! = D.getLast!)
  (hhead : P ≠ [] → P.head! = D.head!) :
-- imply
  let old := A ++ P let new := A ++ D ++ P ons_openTurnSum new + ons_turnPow new.getLast! 0 + 4 + ons_turnPow 0 new.head! = ons_openTurnSum old + ons_turnPow old.getLast! 0 + 4 + ons_turnPow 0 old.head! + ons_cyclicTurnSum D := by
-- proof
  apply StatMech.Onsager.ons_adjustedTurn_insert_cycle A D P hA hD hlast hhead

/--
[ons_ofFn_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_ofFn_ne_nil_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4} :
-- imply
  List.ofFn d ≠ [] := by
-- proof
  apply StatMech.Onsager.ons_ofFn_ne_nil d

/--
[ons_drop_ofFn_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_drop_ofFn_ne_nil_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n} :
-- imply
  (List.ofFn d).drop i.val ≠ [] := by
-- proof
  apply StatMech.Onsager.ons_drop_ofFn_ne_nil d i

/--
[ons_drop_ofFn_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_drop_ofFn_getLast_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n} :
-- imply
  ((List.ofFn d).drop i.val).getLast! = (List.ofFn d).getLast! := by
-- proof
  apply StatMech.Onsager.ons_drop_ofFn_getLast d i

/--
[ons_directionPeriods_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_directionPeriods_getLast_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
-- given
  (hN : 1 ≤ N) :
-- imply
  (ons_directionPeriods d N).getLast! = (List.ofFn d).getLast! := by
-- proof
  apply StatMech.Onsager.ons_directionPeriods_getLast d N hN

/--
[ons_arcInitialBlock_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_arcInitialBlock_getLast_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  ((List.ofFn d).drop imin.val ++ ons_directionPeriods d (N - 1)).getLast! = (List.ofFn d).getLast! := by
-- proof
  apply StatMech.Onsager.ons_arcInitialBlock_getLast d N hN imin

/--
[ons_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_head_eq
  [Inhabited X]
  {l : List X}
-- given
  (h : l ≠ []) :
-- imply
  l.head! = l.head h := by
-- proof
  apply StatMech.Onsager.ons_head l h

/--
[ons_take_ofFn_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_take_ofFn_head_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (h : (List.ofFn d).take i.val ≠ []) :
-- imply
  ((List.ofFn d).take i.val).head! = (List.ofFn d).head! := by
-- proof
  apply StatMech.Onsager.ons_take_ofFn_head d i h

/--
[ons_periodicArc_adjustedTurn_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicArc_adjustedTurn_succ_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {N : ℕ}
  {imin imax : Fin n}
-- given
  (hN : 1 ≤ N) :
-- imply
  let old := ons_periodicArcDirections d N imin imax let new := ons_periodicArcDirections d (N + 1) imin imax ons_openTurnSum new + ons_turnPow new.getLast! 0 + 4 + ons_turnPow 0 new.head! = ons_openTurnSum old + ons_turnPow old.getLast! 0 + 4 + ons_turnPow 0 old.head! + ons_cyclicTurnSum (List.ofFn d) := by
-- proof
  apply StatMech.Onsager.ons_periodicArc_adjustedTurn_succ d N hN imin imax

/--
[ons_periodicSimple_cyclicTurnSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicSimple_cyclicTurnSum_eq_zero_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hinj : Function.Injective (ons_periodStateCoord d))
  (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
-- imply
  ons_cyclicTurnSum (List.ofFn d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_periodicSimple_cyclicTurnSum_eq_zero d hinj hD

/--
[ons_rotatePoint_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_rotatePoint_add_eq
  {c : Fin 4}
  {p q : ℤ × ℤ} :
-- imply
  ons_rotatePoint c (p + q) = ons_rotatePoint c p + ons_rotatePoint c q := by
-- proof
  apply StatMech.Onsager.ons_rotatePoint_add c p q

/--
[ons_rotatePoint_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_rotatePoint_nsmul_eq
  {c : Fin 4}
  {k : ℕ}
  {p : ℤ × ℤ} :
-- imply
  ons_rotatePoint c (k • p) = k • ons_rotatePoint c p := by
-- proof
  apply StatMech.Onsager.ons_rotatePoint_nsmul c k p

/--
[ons_rotatePoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_rotatePoint_injective_eq
  {c : Fin 4} :
-- imply
  Function.Injective (ons_rotatePoint c) := by
-- proof
  apply StatMech.Onsager.ons_rotatePoint_injective c

/--
[ons_stepOf_add_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_stepOf_add_direction_eq
  {c d : Fin 4} :
-- imply
  stepOf (d + c) = ons_rotatePoint c (stepOf d) := by
-- proof
  apply StatMech.Onsager.ons_stepOf_add_direction c d

/--
[ons_pathDisplacement_map_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pathDisplacement_map_add_eq
  {c : Fin 4}
  {l : List (Fin 4)} :
-- imply
  ons_pathDisplacement (l.map (fun d ↦ d + c)) = ons_rotatePoint c (ons_pathDisplacement l) := by
-- proof
  apply StatMech.Onsager.ons_pathDisplacement_map_add c l

/--
[ons_pos_add_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_pos_add_direction_eq
  {n : ℕ}
  [NeZero n]
  {c : Fin 4}
  {d : Fin n → Fin 4}
  {i : Fin n} :
-- imply
  pos (fun j ↦ d j + c) i = ons_rotatePoint c (pos d i) := by
-- proof
  apply StatMech.Onsager.ons_pos_add_direction c d i

/--
[ons_periodStateCoord_add_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodStateCoord_add_direction_eq
  {n : ℕ}
  [NeZero n]
  {c : Fin 4}
  {d : Fin n → Fin 4}
  {z : ℕ × Fin n} :
-- imply
  ons_periodStateCoord (fun i ↦ d i + c) z = ons_rotatePoint c (ons_periodStateCoord d z) := by
-- proof
  apply StatMech.Onsager.ons_periodStateCoord_add_direction c d z

/--
[ons_turnPow_add_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_turnPow_add_both_eq
  {a b c : Fin 4} :
-- imply
  ons_turnPow (a + c) (b + c) = ons_turnPow a b := by
-- proof
  apply StatMech.Onsager.ons_turnPow_add_both a b c

/--
[ons_cyclicTurnSum_ofFn_add_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_cyclicTurnSum_ofFn_add_direction_eq
  {n : ℕ}
  [NeZero n]
  {c : Fin 4}
  {d : Fin n → Fin 4} :
-- imply
  ons_cyclicTurnSum (List.ofFn (fun i ↦ d i + c)) = ons_cyclicTurnSum (List.ofFn d) := by
-- proof
  apply StatMech.Onsager.ons_cyclicTurnSum_ofFn_add_direction c d

/--
[ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hinj : Function.Injective (ons_periodStateCoord d))
  (hne : (ons_pathDisplacement (List.ofFn d)).1 ≠ 0 ∨ (ons_pathDisplacement (List.ofFn d)).2 ≠ 0) :
-- imply
  ons_cyclicTurnSum (List.ofFn d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero d hinj hne

/--
[ons_liftDir_periodStateCoord_eq_periodicLiftVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_liftDir_periodStateCoord_eq_periodicLiftVertex_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my : ℤ}
  {z : ℕ × Fin n}
-- given
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
-- imply
  ons_periodStateCoord (ons_liftDir v) z = ons_periodicLiftVertex v mx my (z.1 : ℤ) z.2 := by
-- proof
  apply StatMech.Onsager.ons_liftDir_periodStateCoord_eq_periodicLiftVertex v mx my hmx hmy z

/--
[ons_liftDir_periodStateCoord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_liftDir_periodStateCoord_injective_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hne : mx ≠ 0 ∨ my ≠ 0)
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
-- imply
  Function.Injective (ons_periodStateCoord (ons_liftDir v)) := by
-- proof
  apply StatMech.Onsager.ons_liftDir_periodStateCoord_injective v hvalid hsite mx my hne hmx hmy

/--
[ons_liftDir_displacement_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_liftDir_displacement_nonzero_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hne : mx ≠ 0 ∨ my ≠ 0)
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
-- imply
  (ons_pathDisplacement (List.ofFn (ons_liftDir v))).1 ≠ 0 ∨ (ons_pathDisplacement (List.ofFn (ons_liftDir v))).2 ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_liftDir_displacement_nonzero v mx my hne hmx hmy

/--
[ons_noncontractible_liftDir_cyclicTurnSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_noncontractible_liftDir_cyclicTurnSum_eq_zero_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
-- imply
  ons_cyclicTurnSum (List.ofFn (ons_liftDir v)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_noncontractible_liftDir_cyclicTurnSum_eq_zero v hvalid hsite hnu hhom

/--
[ons_noncontractible_turnProduct_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_noncontractible_turnProduct_eq_one_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {omega : ℂ}
  {v : Fin n → ons_Dart L}
-- given
  (homega : omega ≠ 0)
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
-- imply
  ∏ k, ons_turnW omega (v (k + 1)).2 (v k).2 = 1 := by
-- proof
  apply StatMech.Onsager.ons_noncontractible_turnProduct_eq_one omega homega v hvalid hsite hnu hhom

/--
[ons_decExpanded_turnProduct_eq_one_of_nonzeroHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean)
-/
@[path]
private lemma ons_decExpanded_turnProduct_eq_one_of_nonzeroHomology_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d)
  (hhom : ons_evenHomology L (ons_walkOriginalEdges q) ≠ 0) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ ∏ k, ons_turnW ons_turnRoot (ons_decExpandedKWLoop L q hq (k + 1)).2 (ons_decExpandedKWLoop L q hq k).2 = 1 := by
-- proof
  apply StatMech.Onsager.ons_decExpanded_turnProduct_eq_one_of_nonzeroHomology L q hq hsnd hhom


-- created on 2026-10-23
