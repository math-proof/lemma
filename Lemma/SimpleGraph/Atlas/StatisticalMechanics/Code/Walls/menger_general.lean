import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.menger_general
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[mngg_connK_of_isConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_connK_of_isConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {P : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hP : mngg_IsConnector ends G a b P) :
-- imply
  connK ends P a b := by
-- proof
  apply StatMech.Walls.mngg_connK_of_isConnector ends hnd hab hP

/--
[mngg_mem_familyUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_mem_familyUnion_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {j : ℕ}
  {P : Fin j → Finset ι}
  {x : ι} :
-- imply
  x ∈ mngg_familyUnion P ↔ ∃ i, x ∈ P i := by
-- proof
  apply StatMech.Walls.mngg_mem_familyUnion

/--
[mngg_familyUnion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_familyUnion_subset_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {j : ℕ}
  {P : Fin j → Finset ι}
-- given
  (hP : mngg_DisjointFamily ends G a b P) :
-- imply
  mngg_familyUnion P ⊆ G := by
-- proof
  apply StatMech.Walls.mngg_familyUnion_subset hP

/--
[mngg_RelConn_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_RelConn_of_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {k k' : ℕ}
-- given
  (hkk' : k ≤ k')
  (h : mngg_RelConn ends G a b k') :
-- imply
  mngg_RelConn ends G a b k := by
-- proof
  apply StatMech.Walls.mngg_RelConn_of_le hkk' h

/--
[mngg_augment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_augment_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {j : ℕ}
  {P : Fin j → Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hP : mngg_DisjointFamily ends G a b P)
  (hres : connK ends (G \ mngg_familyUnion P) a b) :
-- imply
  ∃ Q : Fin (j + 1) → Finset ι, mngg_DisjointFamily ends G a b Q ∧ (∀ i : Fin j, Q i.castSucc = P i) ∧ Q (Fin.last j) ⊆ G \ mngg_familyUnion P := by
-- proof
  apply StatMech.Walls.mngg_augment ends hnd hab hP hres

/--
[mngg_edgeMenger_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_edgeMenger_family_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {k : ℕ}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hconn : mngg_RelConn ends G a b k) :
-- imply
  ∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P := by
-- proof
  apply StatMech.Walls.mngg_edgeMenger_family ends hnd hab k hconn

/--
[mngg_edgeMenger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_edgeMenger_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {k : ℕ}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hconn : mngg_RelConn ends G a b k) :
-- imply
  ∃ P : Fin k → Finset ι, (∀ i, P i ⊆ G) ∧ (∀ i, sources ends (P i) = ({a, b} : Finset W)) ∧ (∀ i, connK ends (P i) a b) ∧ (∀ i i', i ≠ i' → Disjoint (P i) (P i')) := by
-- proof
  apply StatMech.Walls.mngg_edgeMenger ends hnd hab k hconn

/--
[mngg_cut_meets_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_cut_meets_connector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {C P : Finset ι}
-- given
  (hC : mngg_IsCut ends G a b C)
  (hPG : P ⊆ G)
  (hPconn : connK ends P a b) :
-- imply
  (P ∩ C).Nonempty := by
-- proof
  apply StatMech.Walls.mngg_cut_meets_connector ends hC hPG hPconn

/--
[mngg_card_cut_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_card_cut_ge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {k : ℕ}
  {P : Fin k → Finset ι}
  {C : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hP : mngg_DisjointFamily ends G a b P)
  (hC : mngg_IsCut ends G a b C) :
-- imply
  k ≤ #C := by
-- proof
  apply StatMech.Walls.mngg_card_cut_ge ends hnd hab hP hC

/--
[mngg_three_disjoint_connectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_three_disjoint_connectors_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hconn : mngg_RelConn ends G a b 3) :
-- imply
  ∃ P₁ P₂ P₃ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ P₃ ⊆ G ∧ Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧ sources ends P₁ = ({a, b} : Finset W) ∧ sources ends P₂ = ({a, b} : Finset W) ∧ sources ends P₃ = ({a, b} : Finset W) ∧ connK ends P₁ a b ∧ connK ends P₂ a b ∧ connK ends P₃ a b := by
-- proof
  apply StatMech.Walls.mngg_three_disjoint_connectors ends hnd hab hconn

/--
[mngg_maxflow_mincut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_maxflow_mincut_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {a b : W}
  {k : ℕ}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hconn : mngg_RelConn ends G a b k) :
-- imply
  (∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P) ∧ (∀ C : Finset ι, mngg_IsCut ends G a b C → k ≤ #C) := by
-- proof
  apply StatMech.Walls.mngg_maxflow_mincut ends hnd hab k hconn

/--
[mngg_disjoint_connectors_of_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_disjoint_connectors_of_cut_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {x g : W}
  {k : ℕ}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hne : x ≠ g)
  (hconn : mngg_RelConn ends G x g (k + 1)) :
-- imply
  ∃ (P₀ : Finset ι) (P : Fin k → Finset ι), P₀ ⊆ G ∧ connK ends P₀ x g ∧ (∀ i, P i ⊆ G) ∧ (∀ i, connK ends (P i) x g) ∧ (∀ i, Disjoint P₀ (P i)) ∧ (∀ i i', i ≠ i' → Disjoint (P i) (P i')) ∧ (∀ D : Finset ι, D ⊆ mngg_familyUnion P → connK ends (G \ D) x g) := by
-- proof
  apply StatMech.Walls.mngg_disjoint_connectors_of_cut ends hnd hne k hconn

/--
[mngg_theta_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_loopless_eq :
-- imply
  ∀ i : Fin 6, ¬ (mngg_theta i).IsDiag := by
-- proof
  apply StatMech.Walls.mngg_theta_loopless

/--
[mngg_theta_P1_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_P1_sources_eq :
-- imply
  sources mngg_theta ({0} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.mngg_theta_P1_sources

/--
[mngg_theta_P2_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_P2_sources_eq :
-- imply
  sources mngg_theta ({1, 2} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.mngg_theta_P2_sources

/--
[mngg_theta_P3_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_P3_sources_eq :
-- imply
  sources mngg_theta ({3, 4, 5} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.mngg_theta_P3_sources

/--
[mngg_theta_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_disjoint_eq :
-- imply
  Disjoint ({0} : Finset (Fin 6)) ({1, 2} : Finset (Fin 6)) ∧ Disjoint ({0} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6)) ∧ Disjoint ({1, 2} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6)) := by
-- proof
  apply StatMech.Walls.mngg_theta_disjoint

/--
[mngg_theta_P1_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_P1_conn_eq :
-- imply
  connK mngg_theta ({0} : Finset (Fin 6)) 0 4 := by
-- proof
  apply StatMech.Walls.mngg_theta_P1_conn

/--
[mngg_theta_P2_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_P2_conn_eq :
-- imply
  connK mngg_theta ({1, 2} : Finset (Fin 6)) 0 4 := by
-- proof
  apply StatMech.Walls.mngg_theta_P2_conn

/--
[mngg_theta_P3_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_theta_P3_conn_eq :
-- imply
  connK mngg_theta ({3, 4, 5} : Finset (Fin 6)) 0 4 := by
-- proof
  apply StatMech.Walls.mngg_theta_P3_conn

/--
[mngg_test_theta_three_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_test_theta_three_disjoint_eq :
-- imply
  ∃ P₁ P₂ P₃ : Finset (Fin 6), P₁ ⊆ (univ : Finset (Fin 6)) ∧ P₂ ⊆ (univ : Finset (Fin 6)) ∧ P₃ ⊆ (univ : Finset (Fin 6)) ∧ Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧ sources mngg_theta P₁ = ({0, 4} : Finset (Fin 5)) ∧ sources mngg_theta P₂ = ({0, 4} : Finset (Fin 5)) ∧ sources mngg_theta P₃ = ({0, 4} : Finset (Fin 5)) ∧ connK mngg_theta P₁ 0 4 ∧ connK mngg_theta P₂ 0 4 ∧ connK mngg_theta P₃ 0 4 := by
-- proof
  apply StatMech.Walls.mngg_test_theta_three_disjoint

/--
[mngg_test_residual_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_test_residual_conn_eq :
-- imply
  connK mngg_theta ((univ : Finset (Fin 6)) \ ({0, 1, 2} : Finset (Fin 6))) 0 4 := by
-- proof
  apply StatMech.Walls.mngg_test_residual_conn

/--
[mngg_test_cut_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_test_cut_disconnects_eq :
-- imply
  ¬ connK mngg_theta ((univ : Finset (Fin 6)) \ mngg_theta_cut) 0 4 := by
-- proof
  apply StatMech.Walls.mngg_test_cut_disconnects

/--
[mngg_test_maxflow_eq_mincut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_test_maxflow_eq_mincut_eq :
-- imply
  mngg_IsCut mngg_theta (univ : Finset (Fin 6)) 0 4 mngg_theta_cut ∧ #mngg_theta_cut = 3 := by
-- proof
  apply StatMech.Walls.mngg_test_maxflow_eq_mincut

/--
[mngg_sq_cut_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_sq_cut_disconnects_eq :
-- imply
  ¬ connK mngg_sq ((univ : Finset (Fin 4)) \ mngg_sq_cut) 0 2 := by
-- proof
  apply StatMech.Walls.mngg_sq_cut_disconnects

/--
[mngg_test_square_not_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_test_square_not_three_eq :
-- imply
  mngg_IsCut mngg_sq (univ : Finset (Fin 4)) 0 2 mngg_sq_cut ∧ #mngg_sq_cut = 2 ∧ (∀ (P : Fin 3 → Finset (Fin 4)), mngg_DisjointFamily mngg_sq (univ : Finset (Fin 4)) 0 2 P → False) := by
-- proof
  apply StatMech.Walls.mngg_test_square_not_three

/--
[mngg_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean)
-/
@[path]
private lemma mngg_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ) (hconn : mngg_RelConn ends G a b k), ∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {G : Finset ι} {a b : W} (hab : a ≠ b) {k : ℕ} {P : Fin k → Finset ι} (hP : mngg_DisjointFamily ends G a b P) {C : Finset ι} (hC : mngg_IsCut ends G a b C), k ≤ #C) ∧ (∃ P₁ P₂ P₃ : Finset (Fin 6), Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧ connK mngg_theta P₁ 0 4 ∧ connK mngg_theta P₂ 0 4 ∧ connK mngg_theta P₃ 0 4) ∧ (∀ (P : Fin 3 → Finset (Fin 4)), mngg_DisjointFamily mngg_sq (univ : Finset (Fin 4)) 0 2 P → False) := by
-- proof
  apply StatMech.Walls.mngg_status


-- created on 2026-10-23
