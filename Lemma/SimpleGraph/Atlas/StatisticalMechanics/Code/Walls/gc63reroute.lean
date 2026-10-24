import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc63reroute
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc63b_peel_reconn_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_peel_reconn_single_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W} :
-- imply
  ∀ (ds : List ι) (H : Finset ι), gc59_Peelable ends H ds → ∀ (o : ι), o ∈ ds.toFinset → ∀ {p q : W}, ends o = s(p, q) → connK ends (H \ {o}) p q := by
-- proof
  apply StatMech.Walls.gc63b_peel_reconn_single ends

/--
[gc63b_peel_reconn_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_peel_reconn_pair_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W} :
-- imply
  ∀ (ds : List ι) (H : Finset ι), gc59_Peelable ends H ds → ∀ (a b : ι), a ∈ ds.toFinset → b ∈ ds.toFinset → a ≠ b → ∀ {pa qa pb qb : W}, ends a = s(pa, qa) → ends b = s(pb, qb) → connK ends (H \ {a, b}) pa qa ∨ connK ends (H \ {a, b}) pb qb := by
-- proof
  apply StatMech.Walls.gc63b_peel_reconn_pair ends

/--
[gc63b_minConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_minConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D' := by
-- proof
  apply StatMech.Walls.gc63b_minConnector ends hnd K hoy hog hxy hxg hyg huniv hKsrc

/--
[gc63b_disjointConnector_of_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_disjointConnector_of_reroute_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc59_RerouteConnector ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc63b_disjointConnector_of_reroute ends K h

/--
[gc63b_countIneq_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_countIneq_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc57_DisjointConnector ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc63b_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc63b_refut_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_refut_univ_sources_eq :
-- imply
  sources gc63b_refutEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc63b_refut_univ_sources

/--
[gc63b_refut_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_refut_K_sources_eq :
-- imply
  sources gc63b_refutEnds ({0} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc63b_refut_K_sources

/--
[gc63b_refut_V_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_refut_V_sources_eq :
-- imply
  sources gc63b_refutEnds ((univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7))) = ({2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc63b_refut_V_sources

/--
[gc63b_refut_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_refut_loopless_eq :
-- imply
  ∀ i : Fin 7, ¬ (gc63b_refutEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc63b_refut_loopless

/--
[gc63b_conn_1234](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_conn_1234_eq :
-- imply
  connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ ({1, 2, 3, 4} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_conn_1234

/--
[gc63b_conn_1256](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_conn_1256_eq :
-- imply
  connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_conn_1256

/--
[gc63b_conn_3456](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_conn_3456_eq :
-- imply
  connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ ({3, 4, 5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_conn_3456

/--
[gc63b_not_conn_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_not_conn_empty_eq :
-- imply
  ¬ connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ (∅ : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_not_conn_empty

/--
[gc63b_refut_LblockSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_refut_LblockSet_eq :
-- imply
  gc51_LblockSet gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 3 = ({{1, 2, 3, 4}, {1, 2, 5, 6}, {3, 4, 5, 6}} : Finset (Finset (Fin 7))) := by
-- proof
  apply StatMech.Walls.gc63b_refut_LblockSet

/--
[gc63b_not_conn_of_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_not_conn_of_invariant_eq
  {G : Finset (Fin 7)}
  {a b : Fin 5}
  [DecidablePred C]
-- given
  (C : Fin 5 → Prop)
  (hCa : C a)
  (hCb : ¬ C b)
  (hclosed : ∀ c d : Fin 5, C c → (∃ i ∈ G, c ∈ gc63b_refutEnds i ∧ d ∈ gc63b_refutEnds i ∧ c ≠ d) → C d) :
-- imply
  ¬ connK gc63b_refutEnds G a b := by
-- proof
  apply StatMech.Walls.gc63b_not_conn_of_invariant G C hCa hCb hclosed

/--
[gc63b_iso_056_0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_iso_056_0_eq :
-- imply
  ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 2 ∧ ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 3 := by
-- proof
  apply StatMech.Walls.gc63b_iso_056_0

/--
[gc63b_iso_056_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_iso_056_1_eq :
-- imply
  ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 2 ∧ ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_iso_056_1

/--
[gc63b_iso_012_4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_iso_012_4_eq :
-- imply
  ¬ connK gc63b_refutEnds ({0, 1, 2} : Finset (Fin 7)) 2 4 ∧ ¬ connK gc63b_refutEnds ({0, 1, 2} : Finset (Fin 7)) 3 4 := by
-- proof
  apply StatMech.Walls.gc63b_iso_012_4

/--
[gc63b_iso_024_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_iso_024_2_eq :
-- imply
  ¬ connK gc63b_refutEnds ({0, 2, 4} : Finset (Fin 7)) 0 2 ∧ ¬ connK gc63b_refutEnds ({0, 2, 4} : Finset (Fin 7)) 1 2 := by
-- proof
  apply StatMech.Walls.gc63b_iso_024_2

/--
[gc63b_connector_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_connector_cases_eq
  {D : Finset (Fin 7)}
-- given
  (hDV : D ⊆ (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)))
  (hDsrc : sources gc63b_refutEnds D = ({2, 3} : Finset (Fin 5))) :
-- imply
  D = ({1, 2} : Finset (Fin 7)) ∨ D = ({3, 4} : Finset (Fin 7)) ∨ D = ({5, 6} : Finset (Fin 7)) ∨ D = ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
-- proof
  apply StatMech.Walls.gc63b_connector_cases hDV hDsrc

/--
[gc63b_rerouteConnector_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_rerouteConnector_false_eq :
-- imply
  ¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc63b_rerouteConnector_false

/--
[gc63b_D56_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_D56_sources_eq :
-- imply
  sources gc63b_refutEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc63b_D56_sources

/--
[gc63b_sem_1234](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_sem_1234_eq :
-- imply
  connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ ({1, 2, 3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_sem_1234

/--
[gc63b_sem_1256](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_sem_1256_eq :
-- imply
  connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_sem_1256

/--
[gc63b_sem_3456](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_sem_3456_eq :
-- imply
  connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ ({3, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc63b_sem_3456

/--
[gc63b_refut_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_refut_disjointConnector_eq :
-- imply
  gc57_DisjointConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc63b_refut_disjointConnector

/--
[gc63b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean)
-/
@[path]
private lemma gc63b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (ds : List ι) (H : Finset ι), gc59_Peelable ends H ds → ∀ (a b : ι), a ∈ ds.toFinset → b ∈ ds.toFinset → a ≠ b → ∀ {pa qa pb qb : W}, ends a = s(pa, qa) → ends b = s(pb, qb) → connK ends (H \ {a, b}) pa qa ∨ connK ends (H \ {a, b}) pb qb) ∧ (¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3) ∧ gc57_DisjointConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc63b_status


-- created on 2026-10-23
