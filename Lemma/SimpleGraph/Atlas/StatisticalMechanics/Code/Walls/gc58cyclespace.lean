import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc58cyclespace
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc58_disjoint_K_of_subV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_disjoint_K_of_subV_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {K D : Finset ι}
-- given
  (hDV : D ⊆ univ \ K) :
-- imply
  Disjoint K D := by
-- proof
  apply StatMech.Walls.gc58_disjoint_K_of_subV hDV

/--
[gc58_disjointConnector_of_gateInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_disjointConnector_of_gateInK_eq
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
  (hxg : connK ends K x g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc58_disjointConnector_of_gateInK ends K hDV hDsrc hxg

/--
[gc58_removalSurvival_of_gateInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_removalSurvival_of_gateInK_eq
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
  (hxg : connK ends K x g) :
-- imply
  gc55_RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc58_removalSurvival_of_gateInK ends K hDV hDsrc hxg

/--
[gc58_disjointConnector_of_gateInK_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_disjointConnector_of_gateInK_exists_eq
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
  (hxg : connK ends K x g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg

/--
[gc58_disjointConnector_tricho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_disjointConnector_tricho_eq
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
  (hcov : (connK ends K x g) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hcov

/--
[gc58_countIneq_of_tricho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_countIneq_of_tricho_eq
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
  (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), (connK ends K x g) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc58_countIneq_of_tricho ends hnd hox hoy hog hxy hxg' hyg huniv hcov

/--
[gc58_witness_gateInK_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_witness_gateInK_K13_eq :
-- imply
  connK gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 1 3 := by
-- proof
  apply StatMech.Walls.gc58_witness_gateInK_K13

/--
[gc58_witness_gateInK_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_witness_gateInK_K23_eq :
-- imply
  connK gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 1 3 := by
-- proof
  apply StatMech.Walls.gc58_witness_gateInK_K23

/--
[gc58_witness_disjointConnector_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_witness_disjointConnector_K13_eq :
-- imply
  gc57_DisjointConnector gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc58_witness_disjointConnector_K13

/--
[gc58_witness_disjointConnector_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_witness_disjointConnector_K23_eq :
-- imply
  gc57_DisjointConnector gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc58_witness_disjointConnector_K23

/--
[gc58_witness_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_witness_cosetGateDom_eq :
-- imply
  gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc58_witness_cosetGateDom

/--
[gc58_witness_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_witness_perKCount_eq :
-- imply
  gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc58_witness_perKCount

/--
[gc58_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc58cyclespace.lean)
-/
@[path]
private lemma gc58_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) (D : Finset ι), D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → connK ends K x g → gc57_DisjointConnector ends K o x y g) ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc58_status


-- created on 2026-10-23
