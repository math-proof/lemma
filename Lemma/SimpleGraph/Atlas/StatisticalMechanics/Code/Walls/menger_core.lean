import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.menger_core
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[mng_connK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_connK_mono_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K₁ K₂ : Finset ι}
  {a b : W}
-- given
  (h : K₁ ⊆ K₂)
  (hab : connK ends K₁ a b) :
-- imply
  connK ends K₂ a b := by
-- proof
  apply StatMech.Walls.mng_connK_mono ends h hab

/--
[mng_connK_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_connK_of_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P G D : Finset ι}
  {a b : W}
-- given
  (hPG : P ⊆ G)
  (hPD : Disjoint P D)
  (hab : connK ends P a b) :
-- imply
  connK ends (G \ D) a b := by
-- proof
  apply StatMech.Walls.mng_connK_of_disjoint ends hPG hPD hab

/--
[mng_connK_of_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_connK_of_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P : Finset ι}
  {a b : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hP : sources ends P = ({a, b} : Finset W)) :
-- imply
  connK ends P a b := by
-- proof
  apply StatMech.Walls.mng_connK_of_sources ends hnd P hab hP

/--
[mng_sources_symmDiff_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_sources_symmDiff_cycle_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P C : Finset ι}
  {a b : W}
-- given
  (hP : sources ends P = ({a, b} : Finset W))
  (hC : sources ends C = (∅ : Finset W)) :
-- imply
  sources ends (P ∆ C) = ({a, b} : Finset W) := by
-- proof
  apply StatMech.Walls.mng_sources_symmDiff_cycle ends hP hC

/--
[mng_symmDiff_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_symmDiff_connector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P C : Finset ι}
  {a b : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hP : sources ends P = ({a, b} : Finset W))
  (hC : sources ends C = (∅ : Finset W)) :
-- imply
  connK ends (P ∆ C) a b := by
-- proof
  apply StatMech.Walls.mng_symmDiff_connector ends hnd hab hP hC

/--
[mng_exists_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_exists_connector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
-- given
  (hab : connK ends G a b)
  (hne : a ≠ b) :
-- imply
  ∃ P, P ⊆ G ∧ sources ends P = ({a, b} : Finset W) := by
-- proof
  apply StatMech.Walls.mng_exists_connector ends hab hne

/--
[mng_two_disjoint_connectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_two_disjoint_connectors_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hne : a ≠ b)
  (hab : connK ends G a b)
  (hab2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({a, b} : Finset W) → connK ends (G \ P₁) a b) :
-- imply
  ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧ sources ends P₁ = ({a, b} : Finset W) ∧ sources ends P₂ = ({a, b} : Finset W) ∧ connK ends P₁ a b ∧ connK ends P₂ a b := by
-- proof
  apply StatMech.Walls.mng_two_disjoint_connectors ends hnd hne hab hab2

/--
[mng_disjoint_connectors_of_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_disjoint_connectors_of_pairwise_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P G D : Finset ι}
  {x g : W}
-- given
  (hPG : P ⊆ G)
  (hPD : Disjoint P D)
  (hxg : connK ends P x g) :
-- imply
  connK ends (G \ D) x g := by
-- proof
  apply StatMech.Walls.mng_disjoint_connectors_of_pairwise ends hPG hPD hxg

/--
[mng_avoidance_of_two_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_avoidance_of_two_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {x g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hne : x ≠ g)
  (hxg : connK ends G x g)
  (hxg2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({x, g} : Finset W) → connK ends (G \ P₁) x g) :
-- imply
  ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧ connK ends P₂ x g ∧ ∀ D : Finset ι, D ⊆ P₁ → connK ends (G \ D) x g := by
-- proof
  apply StatMech.Walls.mng_avoidance_of_two_disjoint ends hnd hne hxg hxg2

/--
[mng_cyc_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_cyc_loopless_eq :
-- imply
  ∀ i : Fin 4, ¬ (mng_cyc i).IsDiag := by
-- proof
  apply StatMech.Walls.mng_cyc_loopless

/--
[mng_cyc_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_cyc_univ_sources_eq :
-- imply
  sources mng_cyc (univ : Finset (Fin 4)) = (∅ : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.mng_cyc_univ_sources

/--
[mng_cyc_P1_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_cyc_P1_sources_eq :
-- imply
  sources mng_cyc ({0, 1} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.mng_cyc_P1_sources

/--
[mng_cyc_P2_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_cyc_P2_sources_eq :
-- imply
  sources mng_cyc ({2, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.mng_cyc_P2_sources

/--
[mng_cyc_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_cyc_disjoint_eq :
-- imply
  Disjoint ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.mng_cyc_disjoint

/--
[mng_cyc_P1_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_cyc_P1_conn_eq :
-- imply
  connK mng_cyc ({0, 1} : Finset (Fin 4)) 0 2 := by
-- proof
  apply StatMech.Walls.mng_cyc_P1_conn

/--
[mng_cyc_P2_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_cyc_P2_conn_eq :
-- imply
  connK mng_cyc ({2, 3} : Finset (Fin 4)) 0 2 := by
-- proof
  apply StatMech.Walls.mng_cyc_P2_conn

/--
[mng_test_cycle_two_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_test_cycle_two_disjoint_eq :
-- imply
  ∃ P₁ P₂ : Finset (Fin 4), P₁ ⊆ (univ : Finset (Fin 4)) ∧ P₂ ⊆ (univ : Finset (Fin 4)) ∧ Disjoint P₁ P₂ ∧ sources mng_cyc P₁ = ({0, 2} : Finset (Fin 4)) ∧ sources mng_cyc P₂ = ({0, 2} : Finset (Fin 4)) ∧ connK mng_cyc P₁ 0 2 ∧ connK mng_cyc P₂ 0 2 := by
-- proof
  apply StatMech.Walls.mng_test_cycle_two_disjoint

/--
[mng_brg_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_brg_conn_eq :
-- imply
  connK mng_brg (univ : Finset (Fin 2)) 0 2 := by
-- proof
  apply StatMech.Walls.mng_brg_conn

/--
[mng_brg_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_brg_univ_sources_eq :
-- imply
  sources mng_brg (univ : Finset (Fin 2)) = ({0, 2} : Finset (Fin 3)) := by
-- proof
  apply StatMech.Walls.mng_brg_univ_sources

/--
[mng_brg_delete_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_brg_delete_eq_eq :
-- imply
  (univ : Finset (Fin 2)) \ (univ : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by
-- proof
  apply StatMech.Walls.mng_brg_delete_eq

/--
[mng_brg_empty_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_brg_empty_disconn_eq :
-- imply
  ¬ connK mng_brg (∅ : Finset (Fin 2)) 0 2 := by
-- proof
  apply StatMech.Walls.mng_brg_empty_disconn

/--
[mng_test_bridge_no_two_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_test_bridge_no_two_disjoint_eq :
-- imply
  connK mng_brg (univ : Finset (Fin 2)) 0 2 ∧ sources mng_brg (univ : Finset (Fin 2)) = ({0, 2} : Finset (Fin 3)) ∧ ¬ connK mng_brg ((univ : Finset (Fin 2)) \ (univ : Finset (Fin 2))) 0 2 := by
-- proof
  apply StatMech.Walls.mng_test_bridge_no_two_disjoint

/--
[mng_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean)
-/
@[path]
private lemma mng_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {G : Finset ι} {a b : W} (hne : a ≠ b) (hab : connK ends G a b) (hab2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({a, b} : Finset W) → connK ends (G \ P₁) a b), ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧ sources ends P₁ = ({a, b} : Finset W) ∧ sources ends P₂ = ({a, b} : Finset W) ∧ connK ends P₁ a b ∧ connK ends P₂ a b) ∧ (∃ P₁ P₂ : Finset (Fin 4), P₁ ⊆ (univ : Finset (Fin 4)) ∧ P₂ ⊆ (univ : Finset (Fin 4)) ∧ Disjoint P₁ P₂ ∧ connK mng_cyc P₁ 0 2 ∧ connK mng_cyc P₂ 0 2) ∧ (¬ connK mng_brg ((univ : Finset (Fin 2)) \ (univ : Finset (Fin 2))) 0 2) := by
-- proof
  apply StatMech.Walls.mng_status


-- created on 2026-10-23
