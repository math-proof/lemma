import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc19menger
open StatMech StatMech.Walls


/--
[bc19_AFan_c_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_AFan_c_inj_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {A S R : Set V}
  {F : bc19_AFan G A S R k} :
-- imply
  Function.Injective F.c := by
-- proof
  apply StatMech.Walls.bc19_AFan_c_inj F

/--
[bc19_AFan_c_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_AFan_c_cover_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A S R : Set V}
  {F : bc19_AFan G A S R k}
-- given
  (hS : S.ncard = k) :
-- imply
  ∀ s ∈ S, ∃ i, F.c i = s := by
-- proof
  apply StatMech.Walls.bc19_AFan_c_cover hS F

/--
[bc19_match_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_match_spec_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S RA RB : Set V}
  {FA : bc19_AFan G A S RA k}
  {FB : bc19_AFan G B S RB k}
  {i : Fin k}
-- given
  (hS : S.ncard = k) :
-- imply
  FB.c (bc19_match hS FA FB i) = FA.c i := by
-- proof
  apply StatMech.Walls.bc19_match_spec hS FA FB i

/--
[bc19_match_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_match_inj_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S RA RB : Set V}
  {FA : bc19_AFan G A S RA k}
  {FB : bc19_AFan G B S RB k}
-- given
  (hS : S.ncard = k) :
-- imply
  Function.Injective (bc19_match hS FA FB) := by
-- proof
  apply StatMech.Walls.bc19_match_inj hS FA FB

/--
[bc19_Bhalf_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_Bhalf_support_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S RA RB : Set V}
  {FA : bc19_AFan G A S RA k}
  {FB : bc19_AFan G B S RB k}
  {i : Fin k}
-- given
  (hS : S.ncard = k) :
-- imply
  ((FB.q (bc19_match hS FA FB i)).reverse.copy (bc19_match_spec hS FA FB i) rfl).support = (FB.q (bc19_match hS FA FB i)).support.reverse := by
-- proof
  apply StatMech.Walls.bc19_Bhalf_support hS FA FB i

/--
[bc19_gluedPath_support_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_gluedPath_support_mem_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S RA RB : Set V}
  {FA : bc19_AFan G A S RA k}
  {FB : bc19_AFan G B S RB k}
  {i : Fin k}
  {z : V}
-- given
  (hS : S.ncard = k) :
-- imply
  z ∈ (bc19_gluedPath hS FA FB i).support ↔ z ∈ (FA.q i).support ∨ z ∈ (FB.q (bc19_match hS FA FB i)).support := by
-- proof
  apply StatMech.Walls.bc19_gluedPath_support_mem hS FA FB i

/--
[bc19_gluedPath_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_gluedPath_isPath_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S RA RB : Set V}
  {FA : bc19_AFan G A S RA k}
  {FB : bc19_AFan G B S RB k}
  {i : Fin k}
-- given
  (hS : S.ncard = k)
  (hRR : RA ∩ RB ⊆ S) :
-- imply
  (bc19_gluedPath hS FA FB i).IsPath := by
-- proof
  apply StatMech.Walls.bc19_gluedPath_isPath hS hRR FA FB i

/--
[bc19_cross_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_cross_eq_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S RA RB : Set V}
  {FA : bc19_AFan G A S RA k}
  {FB : bc19_AFan G B S RB k}
  {i j : Fin k}
  {z : V}
-- given
  (hS : S.ncard = k)
  (hRR : RA ∩ RB ⊆ S)
  (hzA : z ∈ (FA.q i).support)
  (hzB : z ∈ (FB.q (bc19_match hS FA FB j)).support) :
-- imply
  FA.c i = FA.c j := by
-- proof
  apply StatMech.Walls.bc19_cross_eq hS hRR FA FB hzA hzB

/--
[bc19_aFan_extract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_aFan_extract_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S : Set V}
-- given
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hSsep : bc16_IsSeparator G A B S)
  (hH : bc17_HardDir (bc17_restr G (bc18_AReach G A S)) A S) :
-- imply
  Nonempty (bc19_AFan G A S (bc18_AReach G A S) k) := by
-- proof
  apply StatMech.Walls.bc19_aFan_extract hmin hSsep hH

/--
[bc19_trivFan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_trivFan_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {B S : Set V}
-- given
  (hS : S.ncard = k)
  (hSB : S ⊆ B) :
-- imply
  Nonempty (bc19_AFan G B S S k) := by
-- proof
  apply StatMech.Walls.bc19_trivFan hS hSB

/--
[bc19_lastEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_lastEdge_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {a s : V}
  {Q : G.Walk a s}
-- given
  (hne : a ≠ s) :
-- imply
  ∃ u, G.Adj u s ∧ u ∈ Q.support := by
-- proof
  apply StatMech.Walls.bc19_lastEdge Q hne

/--
[bc19_essential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_essential_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S : Set V}
  {s : V}
-- given
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hScard : S.ncard = k)
  (hsS : s ∈ S) :
-- imply
  ¬ bc16_IsSeparator G A B (S \ {s}) := by
-- proof
  apply StatMech.Walls.bc19_essential hmin hScard hsS

/--
[bc19_Bside_strict_of_notSubsetA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_Bside_strict_of_notSubsetA_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S : Set V}
-- given
  (hSsep : bc16_IsSeparator G A B S)
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hScard : S.ncard = k)
  (hnsub : ¬ S ⊆ A) :
-- imply
  (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard := by
-- proof
  apply StatMech.Walls.bc19_Bside_strict_of_notSubsetA hSsep hmin hScard hnsub

/--
[bc19_Aside_strict_of_notSubsetB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_Aside_strict_of_notSubsetB_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S : Set V}
-- given
  (hSsep : bc16_IsSeparator G A B S)
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hScard : S.ncard = k)
  (hnsub : ¬ S ⊆ B) :
-- imply
  (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard := by
-- proof
  apply StatMech.Walls.bc19_Aside_strict_of_notSubsetB hSsep hmin hScard hnsub

/--
[bc19_directSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_directSolution_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B Y : Set V}
  {x y : V}
-- given
  (hxy : G.Adj x y)
  (hxY : x ∉ Y)
  (hyY : y ∉ Y)
  (hxA : x ∈ A)
  (hyB : y ∈ B)
  (hYA : Y ⊆ A)
  (hYB : Y ⊆ B)
  (hk : Y.ncard + 1 = k) :
-- imply
  Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
-- proof
  apply StatMech.Walls.bc19_directSolution hxy hxY hyY hxA hyB hYA hYB hk

/--
[bc19_Y_sep_of_xyA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_Y_sep_of_xyA_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  {A B Y : Set V}
  {x y : V}
-- given
  (hxY : x ∉ Y)
  (hyY : y ∉ Y)
  (hxA : x ∈ A)
  (hyA : y ∈ A)
  (hYsep : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
-- imply
  bc16_IsSeparator G A B Y := by
-- proof
  apply StatMech.Walls.bc19_Y_sep_of_xyA hxY hyY hxA hyA hYsep

/--
[bc19_subset_AReach_of_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_subset_AReach_of_min_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {A B S : Set V}
-- given
  (hSsep : bc16_IsSeparator G A B S)
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hScard : S.ncard = k) :
-- imply
  S ⊆ bc18_AReach G A S := by
-- proof
  apply StatMech.Walls.bc19_subset_AReach_of_min hSsep hmin hScard

/--
[bc19_getAFan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_getAFan_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {N : ℕ}
  {A B S : Set V}
-- given
  (IH : ∀ (G' : SimpleGraph V), G'.edgeSet.ncard < N → ∀ (A' B' : Set V), bc17_HardDir G' A' B')
  (hltN : (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard → (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N)
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hSsep : bc16_IsSeparator G A B S)
  (hScard : S.ncard = k)
  (hcase : S ⊆ A ∨ ¬ S ⊆ B) :
-- imply
  ∃ RA : Set V, RA ⊆ bc18_AReach G A S ∧ Nonempty (bc19_AFan G A S RA k) := by
-- proof
  apply StatMech.Walls.bc19_getAFan IH hltN hmin hSsep hScard hcase

/--
[bc19_routeS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_routeS_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {N : ℕ}
  {A B S : Set V}
-- given
  (IH : ∀ (G' : SimpleGraph V), G'.edgeSet.ncard < N → ∀ (A' B' : Set V), bc17_HardDir G' A' B')
  (hltA : (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard → (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N)
  (hltB : (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard → (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < N)
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
  (hSsep : bc16_IsSeparator G A B S)
  (hScard : S.ncard = k)
  (hcA : S ⊆ A ∨ ¬ S ⊆ B)
  (hcB : S ⊆ B ∨ ¬ S ⊆ A) :
-- imply
  Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
-- proof
  apply StatMech.Walls.bc19_routeS IH hltA hltB hmin hSsep hScard hcA hcB

/--
[bc19_hardDir_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_hardDir_aux_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {N : ℕ} :
-- imply
  ∀ (G : SimpleGraph V), G.edgeSet.ncard < N → ∀ (A B : Set V), bc17_HardDir G A B := by
-- proof
  apply StatMech.Walls.bc19_hardDir_aux N

/--
[bc19_hardDir_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_hardDir_all_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  {A B : Set V} :
-- imply
  bc17_HardDir G A B := by
-- proof
  apply StatMech.Walls.bc19_hardDir_all G A B

/--
[bc19_menger_minmax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean)
-/
@[path]
private lemma bc19_menger_minmax_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {k : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  {A B : Set V}
  {k : ℕ}
-- given
  (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) :
-- imply
  ∃ F : bc16_DisjointPathFamily G A B (Fin k), ∀ C, bc16_IsSeparator G A B C → Fintype.card (Fin k) ≤ C.ncard := by
-- proof
  apply StatMech.Walls.bc19_menger_minmax G A B hmin


-- created on 2026-10-23
