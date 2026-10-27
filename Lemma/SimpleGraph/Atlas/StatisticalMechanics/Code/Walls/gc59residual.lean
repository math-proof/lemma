import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc59residual.Part4
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc59_reroute_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_reroute_step_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {i : ι}
  {p q : W}
  {a b : W}
-- given
  (hi : i ∈ G)
  (hpq : ends i = s(p, q))
  (hconn : connK ends (G \ {i}) p q)
  (hab : connK ends G a b) :
-- imply
  connK ends (G \ {i}) a b := by
-- proof
  apply StatMech.Walls.gc59_reroute_step ends G i hi hpq hconn hab

/--
[gc59_connK_of_peelable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_connK_of_peelable_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {a b : W} :
-- imply
  ∀ (ds : List ι) (G : Finset ι), gc59_Peelable ends G ds → connK ends G a b → connK ends (gc59_removeList G ds) a b := by
-- proof
  apply StatMech.Walls.gc59_connK_of_peelable ends

/--
[gc59_removeList_eq_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_removeList_eq_sdiff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {G : Finset ι}
  {ds : List ι} :
-- imply
  gc59_removeList G ds = G \ ds.toFinset := by
-- proof
  apply StatMech.Walls.gc59_removeList_eq_sdiff G ds

/--
[gc59_connK_of_peelable_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_connK_of_peelable_sdiff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {a b : W}
  {G : Finset ι}
  {ds : List ι}
-- given
  (hpeel : gc59_Peelable ends G ds)
  (hab : connK ends G a b) :
-- imply
  connK ends (G \ ds.toFinset) a b := by
-- proof
  apply StatMech.Walls.gc59_connK_of_peelable_sdiff ends G ds hpeel hab

/--
[gc59_sdiff_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_sdiff_inter_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {G D : Finset ι} :
-- imply
  G \ (D ∩ G) = G \ D := by
-- proof
  apply StatMech.Walls.gc59_sdiff_inter G D

/--
[gc59_gate_survives_of_peeling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_gate_survives_of_peeling_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {x g : W}
  {ds : List ι}
-- given
  (hds : ds.toFinset = D ∩ (K ∪ L))
  (hpeel : gc59_Peelable ends (K ∪ L) ds)
  (hgate : connK ends (K ∪ L) x g) :
-- imply
  connK ends ((K ∪ L) \ D) x g := by
-- proof
  apply StatMech.Walls.gc59_gate_survives_of_peeling ends hds hpeel hgate

/--
[gc59_disjointConnector_of_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_disjointConnector_of_reroute_eq
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
  apply StatMech.Walls.gc59_disjointConnector_of_reroute ends K h

/--
[gc59_disjointConnector_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_disjointConnector_full_eq
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
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hcov : (connK ends K x g) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc59_RerouteConnector ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc59_disjointConnector_full ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hcov

/--
[gc59_countIneq_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_countIneq_of_cover_eq
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
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), (connK ends K x g) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc59_RerouteConnector ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc59_countIneq_of_cover ends hnd hox hoy hog hxy hxg' hyg huniv hcov

/--
[gc59_witnessEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witnessEnds_univ_sources_eq :
-- imply
  sources gc59_witnessEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc59_witnessEnds_univ_sources

/--
[gc59_witnessEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witnessEnds_K_sources_eq :
-- imply
  sources gc59_witnessEnds ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc59_witnessEnds_K_sources

/--
[gc59_witnessEnds_D_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witnessEnds_D_sources_eq :
-- imply
  sources gc59_witnessEnds ({1, 2} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc59_witnessEnds_D_sources

/--
[gc59_witnessEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witnessEnds_loopless_eq :
-- imply
  ∀ i : Fin 5, ¬ (gc59_witnessEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc59_witnessEnds_loopless

/--
[gc59_witness_conn_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_conn_23_eq :
-- imply
  connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc59_witness_conn_23

/--
[gc59_witness_conn_24](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_conn_24_eq :
-- imply
  connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc59_witness_conn_24

/--
[gc59_witness_conn_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_conn_34_eq :
-- imply
  connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc59_witness_conn_34

/--
[gc59_witness_LblockSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_LblockSet_eq :
-- imply
  gc51_LblockSet gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 3 = ({{2, 3}, {2, 4}, {3, 4}} : Finset (Finset (Fin 5))) := by
-- proof
  apply StatMech.Walls.gc59_witness_LblockSet

/--
[gc59_witness_reconn_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_reconn_23_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ {2}) 0 3 := by
-- proof
  apply StatMech.Walls.gc59_witness_reconn_23

/--
[gc59_witness_reconn_24](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_reconn_24_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ {2}) 0 3 := by
-- proof
  apply StatMech.Walls.gc59_witness_reconn_24

/--
[gc59_witness_rerouteConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_rerouteConnector_eq :
-- imply
  gc59_RerouteConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc59_witness_rerouteConnector

/--
[gc59_witness_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_witness_disjointConnector_eq :
-- imply
  gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc59_witness_disjointConnector

/--
[gc59_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean)
-/
@[path]
private lemma gc59_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (a b : W) (G : Finset ι) (ds : List ι), gc59_Peelable ends G ds → connK ends G a b → connK ends (G \ ds.toFinset) a b) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W), gc59_RerouteConnector ends K o x y g → gc57_DisjointConnector ends K o x y g) ∧ gc59_RerouteConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc59_status


-- created on 2026-10-23
