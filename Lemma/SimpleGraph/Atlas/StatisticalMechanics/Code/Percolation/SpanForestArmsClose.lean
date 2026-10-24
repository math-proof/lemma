import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.SpanForestArmsClose
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[sfa_avoid_no_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_avoid_no_edge_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {x a b : V}
  {w : T.Walk a b}
  {e : Sym2 V}
-- given
  (hx : x ∉ w.support)
  (he : e ∈ w.edges) :
-- imply
  x ∉ e := by
-- proof
  apply StatMech.Percolation.sfa_avoid_no_edge w hx he

/--
[sfa_avoid_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_avoid_walk_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {x a b : V}
-- given
  (ha : a ≠ x)
  (hb : b ≠ x)
  (h : (T.induce ({x}ᶜ : Set V)).Reachable ⟨a, by simpa using ha⟩ ⟨b, by simpa using hb⟩) :
-- imply
  ∃ w : T.Walk a b, x ∉ w.support := by
-- proof
  apply StatMech.Percolation.sfa_avoid_walk ha hb h

/--
[sfa_glue_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_glue_path_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {x c0 c1 z0 z1 : V}
  {w0 : T.Walk c0 z0}
  {w1 : T.Walk c1 z1}
-- given
  (hxc0 : T.Adj x c0)
  (hxc1 : T.Adj x c1)
  (hw0p : w0.IsPath)
  (hw0x : x ∉ w0.support)
  (hw1p : w1.IsPath)
  (hw1x : x ∉ w1.support)
  (hdisj : ∀ v, v ∈ w0.support → v ∈ w1.support → False) :
-- imply
  ∃ p : T.Walk z0 z1, p.IsPath ∧ x ∈ p.support ∧ c0 ∈ p.support ∧ c1 ∈ p.support := by
-- proof
  apply StatMech.Percolation.sfa_glue_path hxc0 hxc1 w0 hw0p hw0x w1 hw1p hw1x hdisj

/--
[sfa_walk_avoid_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_walk_avoid_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {x a b : Site d}
  {w : T.Walk a b}
-- given
  (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
  (hwx : x ∉ w.support) :
-- imply
  Connected d (removeSite x ω) a b := by
-- proof
  apply StatMech.Percolation.sfa_walk_avoid_connected ω T hπ w hwx

/--
[sfa_armWalks_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_armWalks_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {x c0 c1 z0 z1 : Site d}
  {w0 : T.Walk c0 z0}
  {w1 : T.Walk c1 z1}
-- given
  (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
  (hw0x : x ∉ w0.support)
  (hw1x : x ∉ w1.support)
  (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
-- imply
  ∀ v, v ∈ w0.support → v ∈ w1.support → False := by
-- proof
  apply StatMech.Percolation.sfa_armWalks_disjoint ω T hπ w0 hw0x w1 hw1x hcut

/--
[sfa_onBPath_of_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_onBPath_of_arms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  {B : Set (Site d)}
  {x ci cj zi zj : Site d}
  {wi : T.Walk ci zi}
  {wj : T.Walk cj zj}
-- given
  (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
  (hxci : T.Adj x ci)
  (hxcj : T.Adj x cj)
  (hwix : x ∉ wi.support)
  (hzi : zi ∈ B)
  (hwjx : x ∉ wj.support)
  (hzj : zj ∈ B)
  (hcut : ¬ Connected d (removeSite x ω) ci cj) :
-- imply
  spc_OnBPath T B x ∧ spc_OnBPath T B ci ∧ spc_OnBPath T B cj := by
-- proof
  apply StatMech.Percolation.sfa_onBPath_of_arms ω T hπ B hxci hxcj wi hwix hzi wj hwjx hzj hcut

/--
[sfa_spanForestArms_of_armForestReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_spanForestArms_of_armForestReaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : sfa_ArmForestReaching ω n) :
-- imply
  spc_SpanForestArms ω n := by
-- proof
  apply StatMech.Percolation.sfa_spanForestArms_of_armForestReaching ω n h

/--
[sfa_Tcount_le_boundary_of_armForestReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_Tcount_le_boundary_of_armForestReaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : sfa_ArmForestReaching ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.sfa_Tcount_le_boundary_of_armForestReaching ω n h

/--
[sfa_armForestReaching_of_boundary_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_armForestReaching_of_boundary_edge_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b₁ b₂ : Site d}
-- given
  (hb1 : b₁ ∈ vertexBoundary d n)
  (hb2 : b₂ ∈ vertexBoundary d n)
  (hbne : b₁ ≠ b₂)
  (hopen : (openSubgraph d ω).Adj b₁ b₂)
  (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  sfa_ArmForestReaching ω n := by
-- proof
  apply StatMech.Percolation.sfa_armForestReaching_of_boundary_edge ω n hb1 hb2 hbne hopen hnotrif

/--
[sfa_armForestReaching_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean)
-/
@[path]
private lemma sfa_armForestReaching_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
  (habdry : ∀ i, a i ∈ vertexBoundary d n)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a)
  (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧ ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧ ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
-- imply
  sfa_ArmForestReaching ω n := by
-- proof
  apply StatMech.Percolation.sfa_armForestReaching_star ω n a hsingle hadj habdry hxne hainj hsep


-- created on 2026-10-23
