import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.fkc_rqinterface
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fkc_edgeConfig_interface_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqinterface.lean)
-/
@[path]
private lemma fkc_edgeConfig_interface_ge_eq
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
  apply StatMech.Walls.fkc_edgeConfig_interface_ge hci hp hp1 hq

/--
[fkc_neglog_edgeConfig_interface_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqinterface.lean)
-/
@[path]
private lemma fkc_neglog_edgeConfig_interface_le_eq
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
  apply StatMech.Walls.fkc_neglog_edgeConfig_interface_le hci hp hp1 hq

/--
[fkc_factorisation_load_bearing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqinterface.lean)
-/
@[path]
private lemma fkc_factorisation_load_bearing_eq
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
  apply StatMech.Walls.fkc_factorisation_load_bearing hci p q

/--
[fkc_crossInterface_realisable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqinterface.lean)
-/
@[path]
private lemma fkc_crossInterface_realisable_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  fis_CrossInterface (⊥ : SimpleGraph V) (⊥ : SimpleGraph W) (⊥ : SimpleGraph (V ⊕ W)) := by
-- proof
  apply StatMech.Walls.fkc_crossInterface_realisable


-- created on 2026-10-23
