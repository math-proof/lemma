import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc4_revealeqreach
open MeasureTheory Finset StatMech StatMech.Walls


/--
[oc4_notDet_iff_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_notDet_iff_prefix_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {X : ConfigSpace E}
  {e : E} :
-- imply
  ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) ↔ ∃ w : ConfigSpace E, (∀ c ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ), w c = X c) ∧ f w ≠ f X := by
-- proof
  apply StatMech.Walls.oc4_notDet_iff_prefix σ f X e

/--
[oc4_mem_prefix_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_mem_prefix_iff_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {e c : E} :
-- imply
  c ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ) ↔ ∃ s : Fin n, (s : ℕ) < (σ.symm e : ℕ) ∧ σ s = c := by
-- proof
  apply StatMech.Walls.oc4_mem_prefix_iff σ e c

/--
[oc4_reachProb_eq_notDetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_reachProb_eq_notDetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  reachProb μ σ f e = oc4_notDetProb μ σ f e := by
-- proof
  apply StatMech.Walls.oc4_reachProb_eq_notDetProb μ σ f e

/--
[oc4_reveal_eq_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_reveal_eq_reach_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = reachProb μ σ f e ∧ reachProb μ σ f e = oc4_notDetProb μ σ f e := by
-- proof
  apply StatMech.Walls.oc4_reveal_eq_reach hpos hμ1 σ f e

/--
[oc4_reveal_eq_notDetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_reveal_eq_notDetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = oc4_notDetProb μ σ f e := by
-- proof
  apply StatMech.Walls.oc4_reveal_eq_notDetProb hpos hμ1 σ f e

/--
[oc4_notDetProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_notDetProb_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  0 ≤ oc4_notDetProb μ σ f e := by
-- proof
  apply StatMech.Walls.oc4_notDetProb_nonneg hpos σ f e

/--
[oc4_notDetProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_notDetProb_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  oc4_notDetProb μ σ f e ≤ 1 := by
-- proof
  apply StatMech.Walls.oc4_notDetProb_le_one hpos hμ1 σ f e

/--
[oc4_reveal_le_notDetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_reveal_le_notDetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e ≤ oc4_notDetProb μ σ f e := by
-- proof
  apply StatMech.Walls.oc4_reveal_le_notDetProb hpos hμ1 σ f e

/--
[oc4_fk_reveal_eq_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_fk_reveal_eq_reach_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  revealAdapt (fkMass G p q) σ f e = reachProb (fkMass G p q) σ f e ∧ reachProb (fkMass G p q) σ f e = oc4_notDetProb (fkMass G p q) σ f e := by
-- proof
  apply StatMech.Walls.oc4_fk_reveal_eq_reach G hp hp1 hq σ f e

/--
[oc4_fk_reveal_eq_notDetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_fk_reveal_eq_notDetProb_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  revealAdapt (fkMass G p q) σ f e = oc4_notDetProb (fkMass G p q) σ f e := by
-- proof
  apply StatMech.Walls.oc4_fk_reveal_eq_notDetProb G hp hp1 hq σ f e

/--
[oc4_reveal_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean)
-/
@[path]
private lemma oc4_reveal_codingFrame_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X ∧ (∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X) = oc4_notDetProb μ σ f e := by
-- proof
  apply StatMech.Walls.oc4_reveal_codingFrame hpos hμ1 σ f e


-- created on 2026-10-23
