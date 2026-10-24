import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanCycleSpace2
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jcx_faceCount_eq_nullity_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_faceCount_eq_nullity_add_one_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V} :
-- imply
  faceCount K = nullity K + 1 := by
-- proof
  apply StatMech.Lattice.jcx_faceCount_eq_nullity_add_one K

/--
[jcx_nullity_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_nullity_bot_eq
  [Empty.Finite V]
  [DecidableEq V] :
-- imply
  nullity (⊥ : SimpleGraph V) = 0 := by
-- proof
  apply StatMech.Lattice.jcx_nullity_bot

/--
[jcx_whb_bot_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_whb_bot_card_eq :
-- imply
  Nat.card (whb_faceRegion (⊥ : SimpleGraph (Site 2))).ConnectedComponent = 1 := by
-- proof
  apply StatMech.Lattice.jcx_whb_bot_card

/--
[jcx_whb_total_count_of_evenResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_whb_total_count_of_evenResidue_eq
  {P : PlanarZ2Subgraph}
-- given
  (hP : jeb_EvenDegreeSubgraph P)
  (hres : jcx_EvenCountResidue P) :
-- imply
  Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
-- proof
  apply StatMech.Lattice.jcx_whb_total_count_of_evenResidue P hP hres

/--
[jcx_faithfulRegionCount_eq_nullity_of_evenResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_faithfulRegionCount_eq_nullity_of_evenResidue_eq
  {P : PlanarZ2Subgraph}
-- given
  (hP : jeb_EvenDegreeSubgraph P)
  (hres : jcx_EvenCountResidue P) :
-- imply
  whc_faithfulRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.jcx_faithfulRegionCount_eq_nullity_of_evenResidue P hP hres

/--
[jcx_faithfulDiscreteJordan_of_evenResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_faithfulDiscreteJordan_of_evenResidue_eq
  {P : PlanarZ2Subgraph}
-- given
  (hP : jeb_EvenDegreeSubgraph P)
  (hres : jcx_EvenCountResidue P) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jcx_faithfulDiscreteJordan_of_evenResidue P hP hres

/--
[jcx_faithfulCountResidue_of_evenResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_faithfulCountResidue_of_evenResidue_eq
-- given
  (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → jcx_EvenCountResidue P) :
-- imply
  jeb_FaithfulCountResidue := by
-- proof
  apply StatMech.Lattice.jcx_faithfulCountResidue_of_evenResidue h

/--
[jcx_evenCountResidue_of_evenPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_evenCountResidue_of_evenPeel_eq
  {P : PlanarZ2Subgraph}
-- given
  (hpeel : jcx_EvenPeel P) :
-- imply
  jcx_EvenCountResidue P := by
-- proof
  apply StatMech.Lattice.jcx_evenCountResidue_of_evenPeel P hpeel

/--
[jcx_faithfulCountResidue_of_evenPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_faithfulCountResidue_of_evenPeel_eq
-- given
  (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → jcx_EvenPeel P) :
-- imply
  jeb_FaithfulCountResidue := by
-- proof
  apply StatMech.Lattice.jcx_faithfulCountResidue_of_evenPeel h

/--
[jcx_square_dual_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_square_dual_card_eq :
-- imply
  Nat.card (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jcx_square_dual_card

/--
[jcx_square_peel_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_square_peel_witness_eq :
-- imply
  jbc_cyc4 ≤ jbc_Pce.G ∧ jce_ClosedContour (jei_pushGraph jbc_Pce (⊥ : SimpleGraph (Fin 4))).edgeSet ∧ (⊥ : SimpleGraph (Fin 4)).edgeSet.ncard < jbc_cyc4.edgeSet.ncard ∧ faceCount (⊥ : SimpleGraph (Fin 4)) + 1 = faceCount jbc_cyc4 ∧ Nat.card (whb_faceRegion (jei_pushGraph jbc_Pce jbc_Pce.G)).ConnectedComponent = Nat.card (whb_faceRegion (jei_pushGraph jbc_Pce (⊥ : SimpleGraph (Fin 4)))).ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.jcx_square_peel_witness

/--
[jcx_pushGraph_degree_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_pushGraph_degree_corner_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  [Fintype P.V]
  [DecidableRel K.Adj]
  [SimpleGraph.LocallyFinite (jei_pushGraph P K)]
  [SimpleGraph.LocallyFinite K]
  {v : P.V} :
-- imply
  (jei_pushGraph P K).degree (P.emb v) = K.degree v := by
-- proof
  apply StatMech.Lattice.jcx_pushGraph_degree_corner P K v

/--
[jcx_square_even_subgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_square_even_subgraph_eq
  {K : SimpleGraph (Fin 4)}
  [DecidableRel K.Adj]
-- given
  (hle : K ≤ jbc_cyc4)
  (heven : ∀ i, Even (Nat.card (K.neighborSet i))) :
-- imply
  K = ⊥ ∨ K = jbc_cyc4 := by
-- proof
  apply StatMech.Lattice.jcx_square_even_subgraph K hle heven

/--
[jcx_evenPeel_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_evenPeel_unitSquare_eq :
-- imply
  jcx_EvenPeel jbc_Pce := by
-- proof
  apply StatMech.Lattice.jcx_evenPeel_unitSquare

/--
[jcx_faithfulDiscreteJordan_unitSquare_viaPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean)
-/
@[path]
private lemma jcx_faithfulDiscreteJordan_unitSquare_viaPeel_eq :
-- imply
  whc_FaithfulDiscreteJordan jbc_Pce := by
-- proof
  apply StatMech.Lattice.jcx_faithfulDiscreteJordan_unitSquare_viaPeel


-- created on 2026-10-23
