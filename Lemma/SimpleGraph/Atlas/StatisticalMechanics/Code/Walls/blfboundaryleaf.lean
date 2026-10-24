import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.blfboundaryleaf
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[blf_leaf_of_interiorDeg2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean)
-/
@[path]
private lemma blf_leaf_of_interiorDeg2_eq
  [Fintype V]
  [DecidableEq V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {B : V → Prop}
-- given
  (h2 : ∀ v, ¬ B v → 2 ≤ F.degree v) :
-- imply
  ∀ v, F.degree v = 1 → B v := by
-- proof
  apply StatMech.Walls.blf_leaf_of_interiorDeg2 h2

/--
[blf_bc69_of_interiorDeg2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean)
-/
@[path]
private lemma blf_bc69_of_interiorDeg2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  {G : SimpleGraph (↑S : Type)}
  {ιU : Site d → (↑S : Type)}
-- given
  (hSfin : Fintype (↑S : Type))
  (hSne : Nonempty (↑S : Type))
  (hGdec : DecidableRel G.Adj)
  (hac : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hint : ∀ v : (↑S : Type), ((v : Site d) ∉ vertexBoundary d R) → 2 ≤ G.degree v) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.blf_bc69_of_interiorDeg2 ω L R S hSfin hSne G hGdec ιU hac hmin hdeg3 hinj hint

/--
[blf_bc69_of_acyclicArmUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean)
-/
@[path]
private lemma blf_bc69_of_acyclicArmUnion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : blf_AcyclicArmUnion ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.blf_bc69_of_acyclicArmUnion ω L R h

/--
[blf_bk_of_acyclicArmUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean)
-/
@[path]
private lemma blf_bk_of_acyclicArmUnion_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), blf_AcyclicArmUnion ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.blf_bk_of_acyclicArmUnion p hp1 hp0 hdata

/--
[blf_acyclic_closes_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean)
-/
@[path]
private lemma blf_acyclic_closes_witness_eq :
-- imply
  blf_pathG.degree 0 = 1 ∧ blf_pathG.degree 1 = 2 ∧ blf_pathG.degree 2 = 1 ∧ (∀ v : Fin 3, blf_pathG.degree v = 1 → (v = 0 ∨ v = 2)) := by
-- proof
  apply StatMech.Walls.blf_acyclic_closes_witness

/--
[blf_interiorCycle_obstructs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean)
-/
@[path]
private lemma blf_interiorCycle_obstructs_eq :
-- imply
  bof2_advT ≤ bof2_advG ∧ bof2_advT.IsAcyclic ∧ bof2_advG.degree 2 = 2 ∧ bof2_advT.degree 2 = 1 ∧ (2 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.blf_interiorCycle_obstructs

/--
[blf_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean)
-/
@[path]
private lemma blf_status_eq :
-- imply
  (∀ {V : Type} [Fintype V] [DecidableEq V] {F : SimpleGraph V} [_i : DecidableRel F.Adj] {B : V → Prop}, (∀ v, ¬ B v → 2 ≤ F.degree v) → ∀ v, F.degree v = 1 → B v) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), blf_AcyclicArmUnion ω L R → bc69_Gn_globalForest ω L R) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), blf_AcyclicArmUnion ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧ (bof2_advT ≤ bof2_advG ∧ bof2_advT.IsAcyclic ∧ bof2_advG.degree 2 = 2 ∧ bof2_advT.degree 2 = 1 ∧ (2 : Fin 4) ∉ ({0} : Finset (Fin 4))) := by
-- proof
  apply StatMech.Walls.blf_status


-- created on 2026-10-23
