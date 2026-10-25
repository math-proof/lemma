import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.fc_interface
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fc_clusterCount_splits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_interface.lean)
-/
@[path]
private lemma fc_clusterCount_splits_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  numClusters K (fsm_combine σ τ) = numClusters G σ + numClusters H τ := by
-- proof
  apply StatMech.Walls.fc_clusterCount_splits hci σ τ

/--
[fc_factorisation_is_engine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_interface.lean)
-/
@[path]
private lemma fc_factorisation_is_engine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  fkWeight K p q (fsm_combine σ τ) = (1 - p) ^ (fis_interface G H K).card * (fkWeight G p q σ * fkWeight H p q τ) := by
-- proof
  apply StatMech.Walls.fc_factorisation_is_engine hci p q σ τ

/--
[fc_interface_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_interface.lean)
-/
@[path]
private lemma fc_interface_ge_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
-- given
  (hci : fis_CrossInterface G H K)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q) ≤ ecz_fkZEdge K p q := by
-- proof
  apply StatMech.Walls.fc_interface_ge hci hp hp1 hq

/--
[fc_neglog_interface_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_interface.lean)
-/
@[path]
private lemma fc_neglog_interface_le_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
-- given
  (hci : fis_CrossInterface G H K)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  - Real.log (ecz_fkZEdge K p q) ≤ - Real.log (ecz_fkZEdge G p q) + - Real.log (ecz_fkZEdge H p q) - (fis_interface G H K).card * Real.log (1 - p) := by
-- proof
  apply StatMech.Walls.fc_neglog_interface_le hci hp hp1 hq

/--
[fc_lhs_eq_glued_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_interface.lean)
-/
@[path]
private lemma fc_lhs_eq_glued_sum_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q) = ∑ στ : ecz_ClosedOff G × ecz_ClosedOff H, fkWeight K p q (fsm_combine στ.1.val στ.2.val) := by
-- proof
  apply StatMech.Walls.fc_lhs_eq_glued_sum hci p q

/--
[fc_interface_realisable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_interface.lean)
-/
@[path]
private lemma fc_interface_realisable_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  fis_CrossInterface (⊥ : SimpleGraph V) (⊥ : SimpleGraph W) (⊥ : SimpleGraph (V ⊕ W)) := by
-- proof
  apply StatMech.Walls.fc_interface_realisable


-- created on 2026-10-23
