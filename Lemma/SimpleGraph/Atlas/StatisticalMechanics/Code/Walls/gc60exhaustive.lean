import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc60exhaustive.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc60_degK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_degK_mono_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S T : Finset ι}
  {g : W}
-- given
  (hST : S ⊆ T) :
-- imply
  degK ends S g ≤ degK ends T g := by
-- proof
  apply StatMech.Walls.gc60_degK_mono ends hST g

/--
[gc60_degK_zero_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_degK_zero_of_even_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {g : W}
  {S : Finset ι}
-- given
  (hg1 : degK ends (univ : Finset ι) g = 1)
  (hSeven : Even (degK ends S g)) :
-- imply
  degK ends S g = 0 := by
-- proof
  apply StatMech.Walls.gc60_degK_zero_of_even ends hg1 hSeven

/--
[gc60_no_gEdge_of_degZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_no_gEdge_of_degZero_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S : Finset ι}
  {g : W}
-- given
  (hS0 : degK ends S g = 0) :
-- imply
  ∀ i ∈ S, g ∉ ends i := by
-- proof
  apply StatMech.Walls.gc60_no_gEdge_of_degZero ends hS0

/--
[gc60_not_connK_of_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_not_connK_of_isolated_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S : Finset ι}
  {x g : W}
-- given
  (hxg : x ≠ g)
  (hiso : ∀ i ∈ S, g ∉ ends i) :
-- imply
  ¬ connK ends S x g := by
-- proof
  apply StatMech.Walls.gc60_not_connK_of_isolated ends hxg hiso

/--
[gc60_isolated_of_gDegOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_isolated_of_gDegOne_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {L : Finset ι}
-- given
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hg1 : degK ends (univ : Finset ι) g = 1)
  (hLsrc : sources ends L = (∅ : Finset W)) :
-- imply
  ∀ i ∈ K ∪ L, g ∉ ends i := by
-- proof
  apply StatMech.Walls.gc60_isolated_of_gDegOne ends K hog hxg hKsrc hg1 hLsrc

/--
[gc60_lblockSet_empty_of_gDegOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_lblockSet_empty_of_gDegOne_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hg1 : degK ends (univ : Finset ι) g = 1) :
-- imply
  gc51_LblockSet ends K o x g = (∅ : Finset (Finset ι)) := by
-- proof
  apply StatMech.Walls.gc60_lblockSet_empty_of_gDegOne ends K hog hxg hKsrc hg1

/--
[gc60_disjointConnector_of_gDegOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_disjointConnector_of_gDegOne_eq
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
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hg1 : degK ends (univ : Finset ι) g = 1) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg hyg huniv hKsrc hg1

/--
[gc60_cover_of_gateOr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_cover_of_gateOr_eq
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
  (hcov : (connK ends K x g) ∨ (degK ends (univ : Finset ι) g = 1) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc59_RerouteConnector ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc60_cover_of_gateOr ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hcov

/--
[gc60_countIneq_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_countIneq_of_cover_eq
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
  (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), (connK ends K x g) ∨ (degK ends (univ : Finset ι) g = 1) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc59_RerouteConnector ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc60_countIneq_of_cover ends hnd hox hoy hog hxy hxg' hyg huniv hcov

/--
[gc60_gDeg_univ_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_gDeg_univ_odd_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  Odd (degK ends (univ : Finset ι) g) := by
-- proof
  apply StatMech.Walls.gc60_gDeg_univ_odd ends hog hxg hyg huniv

/--
[gc60_gDeg_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_gDeg_dichotomy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  degK ends (univ : Finset ι) g = 1 ∨ 3 ≤ degK ends (univ : Finset ι) g := by
-- proof
  apply StatMech.Walls.gc60_gDeg_dichotomy ends hog hxg hyg huniv

/--
[gc60_cover_reduce_to_parallelG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_cover_reduce_to_parallelG_eq
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
  (hpar : 3 ≤ degK ends (univ : Finset ι) g → (connK ends K x g) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc59_RerouteConnector ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc60_cover_reduce_to_parallelG ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hpar

/--
[gc60_witnessEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witnessEnds_univ_sources_eq :
-- imply
  sources gc60_witnessEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc60_witnessEnds_univ_sources

/--
[gc60_witnessEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witnessEnds_K_sources_eq :
-- imply
  sources gc60_witnessEnds ({0} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc60_witnessEnds_K_sources

/--
[gc60_witnessEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witnessEnds_loopless_eq :
-- imply
  ∀ i : Fin 3, ¬ (gc60_witnessEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc60_witnessEnds_loopless

/--
[gc60_witnessEnds_gDegOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witnessEnds_gDegOne_eq :
-- imply
  degK gc60_witnessEnds (univ : Finset (Fin 3)) (3 : Fin 4) = 1 := by
-- proof
  apply StatMech.Walls.gc60_witnessEnds_gDegOne

/--
[gc60_witness_not_gateInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witness_not_gateInK_eq :
-- imply
  ¬ connK gc60_witnessEnds ({0} : Finset (Fin 3)) 1 3 := by
-- proof
  apply StatMech.Walls.gc60_witness_not_gateInK

/--
[gc60_witness_lblock_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witness_lblock_empty_eq :
-- imply
  gc51_LblockSet gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 3 = (∅ : Finset (Finset (Fin 3))) := by
-- proof
  apply StatMech.Walls.gc60_witness_lblock_empty

/--
[gc60_witness_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witness_disjointConnector_eq :
-- imply
  gc57_DisjointConnector gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc60_witness_disjointConnector

/--
[gc60_witness_no_ygEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_witness_no_ygEdge_eq :
-- imply
  ¬ ∃ i, i ∈ (univ : Finset (Fin 3)) \ ({0} : Finset (Fin 3)) ∧ gc60_witnessEnds i = s(2, 3) := by
-- proof
  apply StatMech.Walls.gc60_witness_no_ygEdge

/--
[gc60_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean)
-/
@[path]
private lemma gc60_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → sources ends K = ({o, x} : Finset W) → degK ends (univ : Finset ι) g = 1 → gc57_DisjointConnector ends K o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (o x y g : W), o ≠ g → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → degK ends (univ : Finset ι) g = 1 ∨ 3 ≤ degK ends (univ : Finset ι) g) ∧ gc51_LblockSet gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 3 = (∅ : Finset (Finset (Fin 3))) ∧ gc57_DisjointConnector gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc60_status


-- created on 2026-10-23
