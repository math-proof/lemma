import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part9
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[shbK4Edge.code_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma code_injective_eq :
-- imply
  Function.Injective shbK4Edge.code := by
-- proof
  apply StatMech.Sharpness.shbK4Edge.code_injective

/--
[shbK4Graph_mem_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4Graph_mem_edgeSet_iff_eq
  {E : Finset shbK4Edge}
  {e : Sym2 (Fin 4)} :
-- imply
  e ∈ (shbK4Graph E).edgeSet ↔ e ∈ E.image shbK4Edge.code := by
-- proof
  apply StatMech.Sharpness.shbK4Graph_mem_edgeSet_iff E e

/--
[shbK4Graph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4Graph_edgeFinset_eq
  {E : Finset shbK4Edge} :
-- imply
  (shbK4Graph E).edgeFinset = E.image shbK4Edge.code := by
-- proof
  apply StatMech.Sharpness.shbK4Graph_edgeFinset E

/--
[shbK4DirectPath_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4DirectPath_support_eq
  {E : Finset shbK4Edge}
-- given
  (h03 : shbK4Edge.e03 ∈ E) :
-- imply
  (shbK4DirectPath E h03).1.support = [(0 : Fin 4), 3] := by
-- proof
  apply StatMech.Sharpness.shbK4DirectPath_support E h03

/--
[shbK4Edge_mem_oddSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4Edge_mem_oddSupport_eq
  {E : Finset shbK4Edge}
  {n : Current (Fin 4)}
  {k : shbK4Edge} :
-- imply
  k ∈ shbK4OddSupport E n ↔ k ∈ E ∧ Odd (n k.code) := by
-- proof
  apply StatMech.Sharpness.shbK4Edge_mem_oddSupport E n k

/--
[shbK4Edge_mem_code_iff_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4Edge_mem_code_iff_incident_eq
  {k : shbK4Edge}
  {v : Fin 4} :
-- imply
  v ∈ k.code ↔ k.Incident v := by
-- proof
  apply StatMech.Sharpness.shbK4Edge_mem_code_iff_incident k v

/--
[shbK4_incidentFlux_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4_incidentFlux_eq_eq
  {E : Finset shbK4Edge}
  {n : Current (Fin 4)}
  {v : Fin 4} :
-- imply
  incidentFlux (shbK4Graph E) n v = ∑ k ∈ E.filter (fun k ↦ k.Incident v), n k.code := by
-- proof
  apply StatMech.Sharpness.shbK4_incidentFlux_eq E n v

/--
[shbK4_sources_eq_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4_sources_eq_boundary_eq
  {E : Finset shbK4Edge}
  {n : Current (Fin 4)} :
-- imply
  sources (shbK4Graph E) n = shbK4Boundary (shbK4OddSupport E n) := by
-- proof
  apply StatMech.Sharpness.shbK4_sources_eq_boundary E n

/--
[shbK4_isBackboneOf_iff_pathSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4_isBackboneOf_iff_pathSupported_eq
  {E : Finset shbK4Edge}
  {n : Current (Fin 4)}
  {x y : Fin 4}
  {p : (shbK4Graph E).Path x y} :
-- imply
  shb_IsBackboneOf (shbK4Graph E) n x y p ↔ shbK4PathSupported (shbK4OddSupport E n) p := by
-- proof
  apply StatMech.Sharpness.shbK4_isBackboneOf_iff_pathSupported E n p

/--
[shbK4_selectsDirect03_iff_realized_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4_selectsDirect03_iff_realized_minimal_eq
  {E A : Finset shbK4Edge}
-- given
  (h03 : shbK4Edge.e03 ∈ E)
  (hAE : A ⊆ E) :
-- imply
  shbK4SelectsDirect03 A ↔ shbK4Boundary A = {0, 3} ∧ shbK4PathSupported A (shbK4DirectPath E h03) ∧ ∀ q : (shbK4Graph E).Path (0 : Fin 4) 3, q.1.support < (shbK4DirectPath E h03).1.support → ¬ shbK4PathSupported A q := by
-- proof
  apply StatMech.Sharpness.shbK4_selectsDirect03_iff_realized_minimal E A h03 hAE

/--
[shb_backboneSelectSupport_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shb_backboneSelectSupport_eq_some_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {p : G.Path x y} :
-- imply
  shb_backboneSelectSupport G n x y = some p ↔ shb_IsBackboneOf G n x y p ∧ ∀ q : G.Path x y, q.1.support < p.1.support → ¬ shb_IsBackboneOf G n x y q := by
-- proof
  apply StatMech.Sharpness.shb_backboneSelectSupport_eq_some_iff G n x y p

/--
[shbK4_source_selector_fiber_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4_source_selector_fiber_iff_eq
  {E : Finset shbK4Edge}
  {n : Current (Fin 4)}
-- given
  (h03 : shbK4Edge.e03 ∈ E) :
-- imply
  (sources (shbK4Graph E) n = {(0 : Fin 4), 3} ∧ shb_backboneSelectSupport (shbK4Graph E) n 0 3 = some (shbK4DirectPath E h03)) ↔ shbK4SelectsDirect03 (shbK4OddSupport E n) := by
-- proof
  apply StatMech.Sharpness.shbK4_source_selector_fiber_iff E h03 n

/--
[shbK4Graph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4Graph_mono_eq
  {E F : Finset shbK4Edge}
-- given
  (hEF : E ⊆ F) :
-- imply
  shbK4Graph E ≤ shbK4Graph F := by
-- proof
  apply StatMech.Sharpness.shbK4Graph_mono hEF

/--
[shbK4H_subset_shbK4G](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4H_subset_shbK4G_eq :
-- imply
  shbK4H ⊆ shbK4G := by
-- proof
  apply StatMech.Sharpness.shbK4H_subset_shbK4G

/--
[shbK4DirectPath_mapLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4DirectPath_mapLe_eq :
-- imply
  shb_pathMapLe (shbK4Graph_mono shbK4H_subset_shbK4G) (shbK4DirectPath shbK4H (by decide)) = shbK4DirectPath shbK4G (by decide) := by
-- proof
  apply StatMech.Sharpness.shbK4DirectPath_mapLe

/--
[shbK4_ofEdgeFun_source_selector_fiber_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4_ofEdgeFun_source_selector_fiber_iff_eq
  {E : Finset shbK4Edge}
  {m : (shbK4Graph E).edgeFinset → ℕ}
-- given
  (h03 : shbK4Edge.e03 ∈ E) :
-- imply
  (sources (shbK4Graph E) (ofEdgeFun (shbK4Graph E) m) = {(0 : Fin 4), 3} ∧ shb_backboneSelectSupport (shbK4Graph E) (ofEdgeFun (shbK4Graph E) m) 0 3 = some (shbK4DirectPath E h03)) ↔ shbK4SelectsDirect03 (shbK4OddSupport E (ofEdgeFun (shbK4Graph E) m)) := by
-- proof
  apply StatMech.Sharpness.shbK4_ofEdgeFun_source_selector_fiber_iff E h03 m

/--
[shbK4_weight_ofEdgeFun_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean)
-/
@[path]
private lemma shbK4_weight_ofEdgeFun_one_eq
  {E : Finset shbK4Edge}
  {x : ℝ}
  {m : (shbK4Graph E).edgeFinset → ℕ} :
-- imply
  weight (shbK4Graph E) x (fun _ ↦ 1) (ofEdgeFun (shbK4Graph E) m) = ∏ k : ↑E, x ^ (m (shbK4GraphEdgeEquiv E k)) / (m (shbK4GraphEdgeEquiv E k)).factorial := by
-- proof
  apply StatMech.Sharpness.shbK4_weight_ofEdgeFun_one E x m


-- created on 2026-10-23
