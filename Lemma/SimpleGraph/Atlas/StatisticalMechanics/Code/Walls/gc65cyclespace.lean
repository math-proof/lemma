import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc65cyclespace.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc65_degK_add_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_degK_add_sdiff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {g : W} :
-- imply
  degK ends (univ : Finset ι) g = degK ends D g + degK ends ((univ : Finset ι) \ D) g := by
-- proof
  apply StatMech.Walls.gc65_degK_add_sdiff ends D g

/--
[gc65_ygConnector_gDeg_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_ygConnector_gDeg_odd_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {y g : W}
-- given
  (hDsrc : sources ends D = ({y, g} : Finset W)) :
-- imply
  Odd (degK ends D g) := by
-- proof
  apply StatMech.Walls.gc65_ygConnector_gDeg_odd ends hDsrc

/--
[gc65_gDegGe3_room](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_gDegGe3_room_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {g : W}
-- given
  (hge3 : 3 ≤ degK ends (univ : Finset ι) g)
  (hD1 : degK ends D g = 1) :
-- imply
  2 ≤ degK ends ((univ : Finset ι) \ D) g := by
-- proof
  apply StatMech.Walls.gc65_gDegGe3_room ends hge3 hD1

/--
[gc65_room_of_gDeg1_ygConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_room_of_gDeg1_ygConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {y g : W}
-- given
  (hge3 : 3 ≤ degK ends (univ : Finset ι) g)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1) :
-- imply
  2 ≤ degK ends ((univ : Finset ι) \ D) g := by
-- proof
  apply StatMech.Walls.gc65_room_of_gDeg1_ygConnector ends hge3 hDsrc hD1

/--
[gc65_disjointConnector_of_gDeg1Connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_disjointConnector_of_gDeg1Connector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc65_GDeg1Connector ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc65_disjointConnector_of_gDeg1Connector ends K h

/--
[gc65_gDeg1Connector_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_gDeg1Connector_of_data_eq
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
  (hD1 : degK ends D g = 1)
  (hL : ∀ L ∈ gc51_LblockSet ends K o x g, ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({x, g} : Finset W) ∧ Disjoint P D ∧ connK ends P x g) :
-- imply
  gc65_GDeg1Connector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc65_gDeg1Connector_of_data ends K hDV hDsrc hD1 hL

/--
[gc65_trim_to_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_trim_to_boundary_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P G D : Finset ι}
  {x g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hxg : x ≠ g)
  (hPG : P ⊆ G)
  (hPD : Disjoint P D)
  (hPconn : connK ends P x g) :
-- imply
  ∃ P', P' ⊆ G ∧ sources ends P' = ({x, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' x g := by
-- proof
  apply StatMech.Walls.gc65_trim_to_boundary ends hnd hxg hPG hPD hPconn

/--
[gc65_disjointConnector_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_disjointConnector_all_eq
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
  (hcov : (connK ends K x g) ∨ (degK ends (univ : Finset ι) g = 1) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc65_GDeg1Connector ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc65_disjointConnector_all ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hcov

/--
[gc65_countIneq_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_countIneq_of_cover_eq
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
  (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), (connK ends K x g) ∨ (degK ends (univ : Finset ι) g = 1) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc65_GDeg1Connector ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc65_countIneq_of_cover ends hnd hox hoy hog hxy hxg' hyg huniv hcov

/--
[gc65_cover_reduce_to_parallelG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_cover_reduce_to_parallelG_eq
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
  (hpar : 3 ≤ degK ends (univ : Finset ι) g → (connK ends K x g) ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g)) ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) ∨ gc65_GDeg1Connector ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc65_cover_reduce_to_parallelG ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hpar

/--
[gc65_witness_gDeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_gDeg_eq :
-- imply
  degK gc59_witnessEnds (univ : Finset (Fin 5)) (3 : Fin 4) = 3 := by
-- proof
  apply StatMech.Walls.gc65_witness_gDeg

/--
[gc65_witness_D_gDeg1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_D_gDeg1_eq :
-- imply
  degK gc59_witnessEnds ({1, 2} : Finset (Fin 5)) (3 : Fin 4) = 1 := by
-- proof
  apply StatMech.Walls.gc65_witness_D_gDeg1

/--
[gc65_witness_room](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_room_eq :
-- imply
  2 ≤ degK gc59_witnessEnds ((univ : Finset (Fin 5)) \ ({1, 2} : Finset (Fin 5))) (3 : Fin 4) := by
-- proof
  apply StatMech.Walls.gc65_witness_room

/--
[gc65_witness_P23_src](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_P23_src_eq :
-- imply
  sources gc59_witnessEnds ({0, 3} : Finset (Fin 5)) = ({1, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc65_witness_P23_src

/--
[gc65_witness_P24_src](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_P24_src_eq :
-- imply
  sources gc59_witnessEnds ({0, 4} : Finset (Fin 5)) = ({1, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc65_witness_P24_src

/--
[gc65_witness_P23_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_P23_conn_eq :
-- imply
  connK gc59_witnessEnds ({0, 3} : Finset (Fin 5)) 1 3 := by
-- proof
  apply StatMech.Walls.gc65_witness_P23_conn

/--
[gc65_witness_P24_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_P24_conn_eq :
-- imply
  connK gc59_witnessEnds ({0, 4} : Finset (Fin 5)) 1 3 := by
-- proof
  apply StatMech.Walls.gc65_witness_P24_conn

/--
[gc65_witness_gDeg1Connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_gDeg1Connector_eq :
-- imply
  gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc65_witness_gDeg1Connector

/--
[gc65_witness_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_witness_disjointConnector_eq :
-- imply
  gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc65_witness_disjointConnector

/--
[gc65_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc65cyclespace.lean)
-/
@[path]
private lemma gc65_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (D : Finset ι) (y g : W), sources ends D = ({y, g} : Finset W) → Odd (degK ends D g)) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (D : Finset ι) (g : W), 3 ≤ degK ends (univ : Finset ι) g → degK ends D g = 1 → 2 ≤ degK ends ((univ : Finset ι) \ D) g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W), gc65_GDeg1Connector ends K o x y g → gc57_DisjointConnector ends K o x y g) ∧ gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc65_status


-- created on 2026-10-23
