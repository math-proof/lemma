import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc55graham.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc55_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_reroute_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K' : Finset ι}
  {i : ι}
  {p q : W}
  {a b : W}
-- given
  (hi : i ∈ K')
  (hpq : ends i = s(p, q))
  (hconn : connK ends (K' \ {i}) p q)
  (hab : connK ends K' a b) :
-- imply
  connK ends (K' \ {i}) a b := by
-- proof
  apply StatMech.Walls.gc55_reroute ends K' i hi hpq hconn hab

/--
[gc55_sources_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_sources_singleton_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {i : ι}
  {y g : W}
-- given
  (hyg : y ≠ g)
  (hi : ends i = s(y, g)) :
-- imply
  sources ends ({i} : Finset ι) = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc55_sources_singleton ends i hyg hi

/--
[gc55_yg_conn_of_removed_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_yg_conn_of_removed_edge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {L : Finset ι}
  {i : ι}
  {y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g)
  (hiL : i ∈ L)
  (hLsrc : sources ends L = (∅ : Finset W))
  (hi : ends i = s(y, g)) :
-- imply
  connK ends (L \ {i}) y g := by
-- proof
  apply StatMech.Walls.gc55_yg_conn_of_removed_edge ends hnd L i hyg hiL hLsrc hi

/--
[gc55_singleEdge_removal_survival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_singleEdge_removal_survival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {i : ι}
  {L : Finset ι}
-- given
  (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
  (hyg : y ≠ g)
  (hiV : i ∈ univ \ K)
  (hi : ends i = s(y, g))
  (hL : L ∈ gc51_LblockSet ends K o x g) :
-- imply
  connK ends (K ∪ (L \ {i})) x g := by
-- proof
  apply StatMech.Walls.gc55_singleEdge_removal_survival ends hnd K hyg hiV hi hL

/--
[gc55_gate_removal_to_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_gate_removal_to_symmDiff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {L D : Finset ι}
  {x g : W}
-- given
  (hgate : connK ends (K ∪ (L \ D)) x g) :
-- imply
  connK ends (K ∪ (L ∆ D)) x g := by
-- proof
  apply StatMech.Walls.gc55_gate_removal_to_symmDiff ends K hgate

/--
[gc55_removalSurvival_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_removalSurvival_of_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
-- imply
  gc55_RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc55_removalSurvival_of_disjoint ends K hDV hDsrc hdisj

/--
[gc55_removalSurvival_of_ygEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_removalSurvival_of_ygEdge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {i : ι}
-- given
  (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
  (hyg : y ≠ g)
  (hiV : i ∈ univ \ K)
  (hi : ends i = s(y, g)) :
-- imply
  gc55_RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc55_removalSurvival_of_ygEdge ends hnd K hyg hiV hi

/--
[gc55_gateShiftInjection_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_gateShiftInjection_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K P₀ : Finset ι}
  {o x y g : W}
-- given
  (hP₀V : P₀ ⊆ univ \ K)
  (hP₀src : sources ends P₀ = ({y, g} : Finset W))
  (h : gc55_RemovalSurvival ends K o x y g) :
-- imply
  gc54_GateShiftInjection ends K P₀ o x g := by
-- proof
  apply StatMech.Walls.gc55_gateShiftInjection_of_removalSurvival ends K P₀ hP₀V hP₀src h

/--
[gc55_cosetGateDom_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_cosetGateDom_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc55_RemovalSurvival ends K o x y g) :
-- imply
  gc53_CosetGateDom ends o x y g := by
-- proof
  apply StatMech.Walls.gc55_cosetGateDom_of_removalSurvival ends h

/--
[gc55_countIneq_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_countIneq_of_removalSurvival_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc55_RemovalSurvival ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc55_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc55_witness_removalSurvival_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_witness_removalSurvival_K13_eq :
-- imply
  gc55_RemovalSurvival gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc55_witness_removalSurvival_K13

/--
[gc55_witness_removalSurvival_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_witness_removalSurvival_K23_eq :
-- imply
  gc55_RemovalSurvival gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc55_witness_removalSurvival_K23

/--
[gc55_witness_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_witness_cosetGateDom_eq :
-- imply
  gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc55_witness_cosetGateDom

/--
[gc55_witness_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_witness_perKCount_eq :
-- imply
  gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc55_witness_perKCount

/--
[gc55_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean)
-/
@[path]
private lemma gc55_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x y g : W), P₀ ⊆ univ \ K → sources ends P₀ = ({y, g} : Finset W) → gc55_RemovalSurvival ends K o x y g → gc54_GateShiftInjection ends K P₀ o x g) ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc55_status


-- created on 2026-10-23
