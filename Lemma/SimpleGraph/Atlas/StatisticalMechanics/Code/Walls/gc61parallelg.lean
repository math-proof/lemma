import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc61parallelg.Part4
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc61_connK_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_connK_singleton_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {i : ι}
  {v g : W}
-- given
  (hvg : v ≠ g)
  (hi : ends i = s(v, g)) :
-- imply
  connK ends ({i} : Finset ι) v g := by
-- proof
  apply StatMech.Walls.gc61_connK_singleton ends hvg hi

/--
[gc61_connK_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_connK_parallel_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {i j : ι}
  {v g : W}
-- given
  (hvg : v ≠ g)
  (hi : ends i = s(v, g)) :
-- imply
  connK ends ({i, j} : Finset ι) v g := by
-- proof
  apply StatMech.Walls.gc61_connK_parallel ends hvg hi

/--
[gc61_sources_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_sources_singleton_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {i : ι}
  {v g : W}
-- given
  (hvg : v ≠ g)
  (hi : ends i = s(v, g)) :
-- imply
  sources ends ({i} : Finset ι) = ({v, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc61_sources_singleton ends i hvg hi

/--
[gc61_relative2conn_of_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_relative2conn_of_parallel_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {i j : ι}
  {v g : W}
  {P₁ : Finset ι}
-- given
  (hij : i ≠ j)
  (hvg : v ≠ g)
  (hi : ends i = s(v, g))
  (hj : ends j = s(v, g))
  (hP₁G : P₁ ⊆ ({i, j} : Finset ι))
  (hP₁src : sources ends P₁ = ({v, g} : Finset W)) :
-- imply
  connK ends (({i, j} : Finset ι) \ P₁) v g := by
-- proof
  apply StatMech.Walls.gc61_relative2conn_of_parallel ends hij hvg hi hj P₁ hP₁G hP₁src

/--
[gc61_two_disjoint_of_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_two_disjoint_of_parallel_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {i j : ι}
  {v g : W}
-- given
  (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
  (hij : i ≠ j)
  (hvg : v ≠ g)
  (hi : ends i = s(v, g))
  (hj : ends j = s(v, g)) :
-- imply
  ∃ P₁ P₂ : Finset ι, P₁ ⊆ ({i, j} : Finset ι) ∧ P₂ ⊆ ({i, j} : Finset ι) ∧ Disjoint P₁ P₂ ∧ sources ends P₁ = ({v, g} : Finset W) ∧ sources ends P₂ = ({v, g} : Finset W) ∧ connK ends P₁ v g ∧ connK ends P₂ v g := by
-- proof
  apply StatMech.Walls.gc61_two_disjoint_of_parallel ends hnd hij hvg hi hj

/--
[gc61_parallel_reconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_parallel_reconnect_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {i j : ι}
  {v g : W}
-- given
  (hij : i ≠ j)
  (hvg : v ≠ g)
  (hj : ends j = s(v, g))
  (hjG : j ∈ G) :
-- imply
  connK ends (G \ {i}) v g := by
-- proof
  apply StatMech.Walls.gc61_parallel_reconnect ends hij hvg hj hjG

/--
[gc61_rerouteConnector_of_parallelTwin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_rerouteConnector_of_parallelTwin_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc61_ParallelTwinPresent ends K o x y g) :
-- imply
  gc59_RerouteConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc61_rerouteConnector_of_parallelTwin ends K h

/--
[gc61_disjointConnector_of_parallelTwin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_disjointConnector_of_parallelTwin_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc61_ParallelTwinPresent ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc61_disjointConnector_of_parallelTwin ends K h

/--
[gc61_disjointConnector_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_disjointConnector_all_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hcov : (connK ends K x g) ∨ (degK ends (univ : Finset ι) g = 1) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc61_ParallelTwinPresent ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc61_disjointConnector_all ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hcov

/--
[gc61_countIneq_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_countIneq_of_cover_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), (connK ends K x g) ∨ (degK ends (univ : Finset ι) g = 1) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc61_ParallelTwinPresent ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc61_countIneq_of_cover ends hnd hox hoy hog hxy hxg' hyg huniv hcov

/--
[gc61_gStar_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_gStar_univ_sources_eq :
-- imply
  sources gc61_gStar (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc61_gStar_univ_sources

/--
[gc61_gStar_gDeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_gStar_gDeg_eq :
-- imply
  degK gc61_gStar (univ : Finset (Fin 3)) (3 : Fin 4) = 3 := by
-- proof
  apply StatMech.Walls.gc61_gStar_gDeg

/--
[gc61_gStar_xg_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_gStar_xg_conn_eq :
-- imply
  connK gc61_gStar (univ : Finset (Fin 3)) 1 3 := by
-- proof
  apply StatMech.Walls.gc61_gStar_xg_conn

/--
[gc61_gStar_P1_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_gStar_P1_sources_eq :
-- imply
  sources gc61_gStar ({1} : Finset (Fin 3)) = ({1, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc61_gStar_P1_sources

/--
[gc61_gStar_delete_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_gStar_delete_eq_eq :
-- imply
  (univ : Finset (Fin 3)) \ ({1} : Finset (Fin 3)) = ({0, 2} : Finset (Fin 3)) := by
-- proof
  apply StatMech.Walls.gc61_gStar_delete_eq

/--
[gc61_gStar_delete_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_gStar_delete_disconn_eq :
-- imply
  ¬ connK gc61_gStar ({0, 2} : Finset (Fin 3)) 1 3 := by
-- proof
  apply StatMech.Walls.gc61_gStar_delete_disconn

/--
[gc61_relative2conn_of_gDegGe3_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_relative2conn_of_gDegGe3_false_eq :
-- imply
  ∃ (ends : Fin 3 → Sym2 (Fin 4)) (P₁ : Finset (Fin 3)), sources ends (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ 3 ≤ degK ends (univ : Finset (Fin 3)) (3 : Fin 4) ∧ connK ends (univ : Finset (Fin 3)) 1 3 ∧ P₁ ⊆ (univ : Finset (Fin 3)) ∧ sources ends P₁ = ({1, 3} : Finset (Fin 4)) ∧ ¬ connK ends ((univ : Finset (Fin 3)) \ P₁) 1 3 := by
-- proof
  apply StatMech.Walls.gc61_relative2conn_of_gDegGe3_false

/--
[gc61_gStar_rel2_x_g_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_gStar_rel2_x_g_fails_eq :
-- imply
  ¬ (∀ P₁ : Finset (Fin 3), P₁ ⊆ (univ : Finset (Fin 3)) → sources gc61_gStar P₁ = ({1, 3} : Finset (Fin 4)) → connK gc61_gStar ((univ : Finset (Fin 3)) \ P₁) 1 3) := by
-- proof
  apply StatMech.Walls.gc61_gStar_rel2_x_g_fails

/--
[gc61_parWit_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_parWit_loopless_eq :
-- imply
  ∀ k : Fin 2, ¬ (gc61_parWit k).IsDiag := by
-- proof
  apply StatMech.Walls.gc61_parWit_loopless

/--
[gc61_parWit_two_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_parWit_two_disjoint_eq :
-- imply
  ∃ P₁ P₂ : Finset (Fin 2), P₁ ⊆ ({0, 1} : Finset (Fin 2)) ∧ P₂ ⊆ ({0, 1} : Finset (Fin 2)) ∧ Disjoint P₁ P₂ ∧ sources gc61_parWit P₁ = ({0, 3} : Finset (Fin 4)) ∧ sources gc61_parWit P₂ = ({0, 3} : Finset (Fin 4)) ∧ connK gc61_parWit P₁ 0 3 ∧ connK gc61_parWit P₂ 0 3 := by
-- proof
  apply StatMech.Walls.gc61_parWit_two_disjoint

/--
[gc61_witness_parallelTwin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_witness_parallelTwin_eq :
-- imply
  gc61_ParallelTwinPresent gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc61_witness_parallelTwin

/--
[gc61_witness_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_witness_disjointConnector_eq :
-- imply
  gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc61_witness_disjointConnector

/--
[gc61_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean)
-/
@[path]
private lemma gc61_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (i j : ι) (v g : W), i ≠ j → v ≠ g → ends i = s(v, g) → ends j = s(v, g) → ∀ P₁ : Finset ι, P₁ ⊆ ({i, j} : Finset ι) → sources ends P₁ = ({v, g} : Finset W) → connK ends (({i, j} : Finset ι) \ P₁) v g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W), gc61_ParallelTwinPresent ends K o x y g → gc57_DisjointConnector ends K o x y g) ∧ (∃ (ends : Fin 3 → Sym2 (Fin 4)) (P₁ : Finset (Fin 3)), 3 ≤ degK ends (univ : Finset (Fin 3)) (3 : Fin 4) ∧ connK ends (univ : Finset (Fin 3)) 1 3 ∧ sources ends P₁ = ({1, 3} : Finset (Fin 4)) ∧ ¬ connK ends ((univ : Finset (Fin 3)) \ P₁) 1 3) ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc61_status


-- created on 2026-10-23
