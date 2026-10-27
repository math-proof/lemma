import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentTranslation
open Set Finset SimpleGraph StatMech StatMech.OSSS StatMech.OSSS.RevealmentTranslation


/--
[siteRadius_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma siteRadius_le_iff_eq
  {d n : ℕ}
  {x : Site d} :
-- imply
  siteRadius x ≤ n ↔ ∀ i, (x i).natAbs ≤ n := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.siteRadius_le_iff

/--
[mem_box_iff_siteRadius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma mem_box_iff_siteRadius_le_eq
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ box d n ↔ siteRadius x ≤ n := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.mem_box_iff_siteRadius_le

/--
[siteRadius_eq_of_mem_vertexBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma siteRadius_eq_of_mem_vertexBoundary_eq
  {d k : ℕ}
  {x : Site d}
-- given
  (hx : x ∈ vertexBoundary d k) :
-- imply
  siteRadius x = k := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.siteRadius_eq_of_mem_vertexBoundary hx

/--
[centeredRadius_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma centeredRadius_self_eq
  {d : ℕ}
  {u : Site d} :
-- imply
  centeredRadius u u = 0 := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.centeredRadius_self u

/--
[centeredRadius_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma centeredRadius_comm_eq
  {d : ℕ}
  {u v : Site d} :
-- imply
  centeredRadius u v = centeredRadius v u := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.centeredRadius_comm u v

/--
[siteRadius_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma siteRadius_triangle_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  siteRadius x ≤ siteRadius y + centeredRadius y x := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.siteRadius_triangle x y

/--
[centeredRadius_step_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma centeredRadius_step_le_eq
  {d : ℕ}
  {u x y : Site d}
-- given
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  centeredRadius u y ≤ centeredRadius u x + 1 := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.centeredRadius_step_le u x y hxy

/--
[nat_discrete_ivt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma nat_discrete_ivt_eq
  {f : ℕ → ℕ} :
-- imply
  ∀ n, f 0 = 0 → (∀ i, i < n → f (i + 1) ≤ f i + 1) → ∀ m, m ≤ f n → ∃ i ≤ n, f i = m := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.nat_discrete_ivt f

/--
[openWalk_hits_centeredBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma openWalk_hits_centeredBoundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
  {w : (openSubgraph d ω).Walk u v}
  {m : ℕ}
-- given
  (hm : m ≤ centeredRadius u v) :
-- imply
  ∃ z ∈ centeredBoundary u m, Connected d ω u z := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.openWalk_hits_centeredBoundary w hm

/--
[connectedToSet_originBoundary_imp_centered_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma connectedToSet_originBoundary_imp_centered_of_le_eq
  {d k m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u : Site d}
-- given
  (hm : m ≤ ((k : ℤ) - (siteRadius u : ℤ)).natAbs) :
-- imply
  ConnectedToSet d ω u (vertexBoundary d k) → ConnectedToSet d ω u (centeredBoundary u m) := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.connectedToSet_originBoundary_imp_centered_of_le hm

/--
[connectedToSet_originBoundary_imp_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma connectedToSet_originBoundary_imp_centered_eq
  {d k : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u : Site d} :
-- imply
  ConnectedToSet d ω u (vertexBoundary d k) → ConnectedToSet d ω u (centeredBoundary u (((k : ℤ) - (siteRadius u : ℤ)).natAbs)) := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.connectedToSet_originBoundary_imp_centered

/--
[sum_Icc_one_pred_eq_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma sum_Icc_one_pred_eq_sum_range_eq
  {f : ℕ → ℝ}
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.Icc 1 n, f (k - 1) = ∑ j ∈ Finset.range n, f j := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.sum_Icc_one_pred_eq_sum_range f n

/--
[mean_indicator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma mean_indicator_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [DecidablePred P]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (P : ConfigSpace E → Prop) :
-- imply
  0 ≤ Lindeberg.mean μ (fun ω => if P ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.mean_indicator_nonneg hμ0 P

/--
[revealment_sum_bound_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentTranslation.lean)
-/
@[path]
private lemma revealment_sum_bound_lattice_eq
  [Fintype E]
  [DecidableEq E]
  {d n : ℕ}
  {μ : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {Λ : Finset (Site d)}
  {u : Site d}
  [∀ (ω : ConfigSpace E) (x : Site d) (k : ℕ), Decidable (ConnectedToSet d (liftCfg edge ω) x (vertexBoundary d k))]
  [∀ (ω : ConfigSpace E) (x : Site d) (k : ℕ), Decidable (ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x k))]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hne : Λ.Nonempty)
  (hu : u ∈ Λ)
  (hubox : u ∈ box d n) :
-- imply
  (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) u (vertexBoundary d k) then (1 : ℝ) else 0)) ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j) then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.OSSS.RevealmentTranslation.revealment_sum_bound_lattice μ hμ0 edge Λ hne u hu hubox


-- created on 2026-10-23
