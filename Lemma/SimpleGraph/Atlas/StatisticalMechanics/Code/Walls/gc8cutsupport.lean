import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc8cutsupport
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc8_not_internal_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_not_internal_both_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {e : Sym2 V}
-- given
  (h0 : acwInternal S e)
  (h1 : acwInternal Sᶜ e) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.gc8_not_internal_both G S e h0 h1

/--
[gc8_cut_no_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_cut_no_crossing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {e : Sym2 V}
-- given
  (hcut : acwClosedCut G S)
  (he : e ∈ G.edgeFinset) :
-- imply
  ¬ gc8Crosses S e := by
-- proof
  apply StatMech.Walls.gc8_cut_no_crossing G S hcut e he

/--
[gc8_restrict_internal_vanishes_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_restrict_internal_vanishes_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
  {e : Sym2 V}
-- given
  (hv : ∃ v ∈ e, v ∉ S) :
-- imply
  acwRestrict (acwInternal S) n e = 0 := by
-- proof
  apply StatMech.Walls.gc8_restrict_internal_vanishes_cross G S n e hv

/--
[gc8_restrict_external_vanishes_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_restrict_external_vanishes_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
  {e : Sym2 V}
-- given
  (hu : ∃ u ∈ e, u ∈ S) :
-- imply
  acwRestrict (acwInternal Sᶜ) n e = 0 := by
-- proof
  apply StatMech.Walls.gc8_restrict_external_vanishes_cross G S n e hu

/--
[gc8_restrict_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_restrict_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred p]
  {n : Ising.Current V}
  {e : Sym2 V}
-- given
  (p : Sym2 V → Prop) :
-- imply
  n e = acwRestrict p n e + acwRestrict (fun e => ¬ p e) n e := by
-- proof
  apply StatMech.Walls.gc8_restrict_add G p n e

/--
[gc8_offS_eq_externalS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_offS_eq_externalS_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
  {e : Sym2 V}
-- given
  (hcut : acwClosedCut G S)
  (he : e ∈ G.edgeFinset) :
-- imply
  acwRestrict (fun e => ¬ acwInternal S e) n e = acwRestrict (acwInternal Sᶜ) n e := by
-- proof
  apply StatMech.Walls.gc8_offS_eq_externalS G S hcut n e he

/--
[gc8_current_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_current_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
  {e : Sym2 V}
-- given
  (hcut : acwClosedCut G S)
  (he : e ∈ G.edgeFinset) :
-- imply
  n e = acwRestrict (acwInternal S) n e + acwRestrict (acwInternal Sᶜ) n e := by
-- proof
  apply StatMech.Walls.gc8_current_split G S hcut n e he

/--
[gc8_sources_internal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_sources_internal_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G (acwRestrict (acwInternal S) n) = S ∩ Sharpness.sources G n := by
-- proof
  apply StatMech.Walls.gc8_sources_internal_eq G S hcut n

/--
[gc8_sources_external_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_sources_external_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = Sᶜ ∩ Sharpness.sources G n := by
-- proof
  apply StatMech.Walls.gc8_sources_external_eq G S hcut n

/--
[gc8_sources_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_sources_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  Sharpness.sources G n = Sharpness.sources G (acwRestrict (acwInternal S) n) ∪ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n)) (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)) := by
-- proof
  apply StatMech.Walls.gc8_sources_split G S hcut n

/--
[gc8_cutSupportDecomp_of_closedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_cutSupportDecomp_of_closedCut_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  gc8_cutSupportDecomp G S n₁ n₂ := by
-- proof
  apply StatMech.Walls.gc8_cutSupportDecomp_of_closedCut G S hcut n₁ n₂

/--
[gc8_current_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_current_decomp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  (∀ e ∈ G.edgeFinset, ¬ gc8Crosses S e) ∧ (∀ e ∈ G.edgeFinset, n e = acwRestrict (acwInternal S) n e + acwRestrict (acwInternal Sᶜ) n e) ∧ Sharpness.sources G (acwRestrict (acwInternal S) n) = S ∩ Sharpness.sources G n ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = Sᶜ ∩ Sharpness.sources G n ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n)) (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)) := by
-- proof
  apply StatMech.Walls.gc8_current_decomp G S hcut n

/--
[gc8_closedCut_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_closedCut_bot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V} :
-- imply
  acwClosedCut (⊥ : SimpleGraph V) S := by
-- proof
  apply StatMech.Walls.gc8_closedCut_bot G S

/--
[gc8_cutSupportDecomp_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean)
-/
@[path]
private lemma gc8_cutSupportDecomp_bot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n₁ n₂ : Ising.Current V} :
-- imply
  gc8_cutSupportDecomp (⊥ : SimpleGraph V) S n₁ n₂ := by
-- proof
  apply StatMech.Walls.gc8_cutSupportDecomp_bot G S n₁ n₂


-- created on 2026-10-23
