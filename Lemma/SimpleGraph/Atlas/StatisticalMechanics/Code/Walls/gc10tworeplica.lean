import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10tworeplica
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc10_twoReplicaCutDecomp_of_closedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplicaCutDecomp_of_closedCut_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  gc10_twoReplicaCutDecomp G β J S n₁ n₂ := by
-- proof
  apply StatMech.Walls.gc10_twoReplicaCutDecomp_of_closedCut G β J S hcut n₁ n₂

/--
[gc10_twoReplica_fourMark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplica_fourMark_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
  {o x y g : V}
-- given
  (hcut : acwClosedCut G S)
  (hsrc : gc10_combinedSources G n₁ n₂ o x y g) :
-- imply
  gc10_twoReplicaCutDecomp G β J S n₁ n₂ ∧ gc10_combinedSources G n₁ n₂ o x y g := by
-- proof
  apply StatMech.Walls.gc10_twoReplica_fourMark G β J S hcut n₁ n₂ o x y g hsrc

/--
[gc10_twoReplica_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplica_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
  {e : Sym2 V}
-- given
  (hcut : acwClosedCut G S)
  (he : e ∈ G.edgeFinset) :
-- imply
  n₁ e = acwRestrict (acwInternal S) n₁ e + acwRestrict (acwInternal Sᶜ) n₁ e ∧ n₂ e = acwRestrict (acwInternal S) n₂ e + acwRestrict (acwInternal Sᶜ) n₂ e := by
-- proof
  apply StatMech.Walls.gc10_twoReplica_split G S hcut n₁ n₂ e he

/--
[gc10_twoReplica_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplica_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  (Sharpness.sources G (acwRestrict (acwInternal S) n₁) = S ∩ Sharpness.sources G n₁ ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₁) = Sᶜ ∩ Sharpness.sources G n₁) ∧ (Sharpness.sources G (acwRestrict (acwInternal S) n₂) = S ∩ Sharpness.sources G n₂ ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n₂) = Sᶜ ∩ Sharpness.sources G n₂) := by
-- proof
  apply StatMech.Walls.gc10_twoReplica_boundary G S hcut n₁ n₂

/--
[gc10_twoReplica_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplica_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  weight G β J n₁ = weight G β J (acwRestrict (acwInternal Sᶜ) n₁) * weight G β J (acwRestrict (acwInternal S) n₁) ∧ weight G β J n₂ = weight G β J (acwRestrict (acwInternal Sᶜ) n₂) * weight G β J (acwRestrict (acwInternal S) n₂) := by
-- proof
  apply StatMech.Walls.gc10_twoReplica_weight G β J S hcut n₁ n₂

/--
[gc10_twoReplica_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplica_weight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weight G β J (acwRestrict (acwInternal Sᶜ) n₁) ∧ 0 ≤ weight G β J (acwRestrict (acwInternal S) n₁) ∧ 0 ≤ weight G β J (acwRestrict (acwInternal Sᶜ) n₂) ∧ 0 ≤ weight G β J (acwRestrict (acwInternal S) n₂) := by
-- proof
  apply StatMech.Walls.gc10_twoReplica_weight_nonneg G β J hβ hJ S n₁ n₂

/--
[gc10_twoReplica_jointWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplica_jointWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {n₁ n₂ : Ising.Current V}
-- given
  (hcut : acwClosedCut G S) :
-- imply
  weight G β J n₁ * weight G β J n₂ = (weight G β J (acwRestrict (acwInternal Sᶜ) n₁) * weight G β J (acwRestrict (acwInternal S) n₁)) * (weight G β J (acwRestrict (acwInternal Sᶜ) n₂) * weight G β J (acwRestrict (acwInternal S) n₂)) := by
-- proof
  apply StatMech.Walls.gc10_twoReplica_jointWeight G β J S hcut n₁ n₂

/--
[gc10_twoReplica_jointMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplica_jointMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ : Ising.Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weight G β J n₁ * weight G β J n₂ := by
-- proof
  apply StatMech.Walls.gc10_twoReplica_jointMass_nonneg G β J hβ hJ n₁ n₂

/--
[gc10_combinedSources_iff_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_combinedSources_iff_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n₁ n₂ : Ising.Current V}
  {o x y g : V} :
-- imply
  gc10_combinedSources G n₁ n₂ o x y g ↔ Ising.sources G.edgeFinset n₁ ∆ Ising.sources G.edgeFinset n₂ = {o, x, y, g} := by
-- proof
  apply StatMech.Walls.gc10_combinedSources_iff_symmDiff G n₁ n₂ o x y g

/--
[gc10_twoReplicaCutDecomp_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplicaCutDecomp_bot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (V) → ℝ}
  {S : Finset V}
  {n₁ n₂ : Ising.Current V} :
-- imply
  gc10_twoReplicaCutDecomp (⊥ : SimpleGraph V) β J S n₁ n₂ := by
-- proof
  apply StatMech.Walls.gc10_twoReplicaCutDecomp_bot G β J S n₁ n₂

/--
[gc10_twoReplicaCutDecomp_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10tworeplica.lean)
-/
@[path]
private lemma gc10_twoReplicaCutDecomp_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ : Ising.Current V} :
-- imply
  gc10_twoReplicaCutDecomp G β J (∅ : Finset V) n₁ n₂ := by
-- proof
  apply StatMech.Walls.gc10_twoReplicaCutDecomp_empty G β J n₁ n₂


-- created on 2026-10-23
