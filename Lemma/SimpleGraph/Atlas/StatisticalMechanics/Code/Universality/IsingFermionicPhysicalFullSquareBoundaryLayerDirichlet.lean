import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[vertexGhostConductance_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexGhostConductance_nonneg_eq
  {n : Nat} :
-- imply
  ∀ x y, 0 ≤ vertexGhostConductance n x y := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostConductance_nonneg n

/--
[vertexGhostConductance_pos_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexGhostConductance_pos_of_adj_eq
  {n : Nat} :
-- imply
  ∀ ⦃x y⦄, (vertexGhostGraph n).Adj x y → 0 < vertexGhostConductance n x y := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostConductance_pos_of_adj n

/--
[vertexGhost_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexGhost_reaches_boundary_eq
  {n : Nat} :
-- imply
  ∀ x, ∃ b, vertexDirichletBoundary n b ∧ (vertexGhostGraph n).Reachable x b := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhost_reaches_boundary n

/--
[faceGhostConductance_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceGhostConductance_nonneg_eq
  {n : Nat} :
-- imply
  ∀ x y, 0 ≤ faceGhostConductance n x y := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostConductance_nonneg n

/--
[faceGhostConductance_pos_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceGhostConductance_pos_of_adj_eq
  {n : Nat} :
-- imply
  ∀ ⦃x y⦄, (faceGhostGraph n).Adj x y → 0 < faceGhostConductance n x y := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostConductance_pos_of_adj n

/--
[faceGhost_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceGhost_reaches_boundary_eq
  {n : Nat} :
-- imply
  ∀ x, ∃ b, faceDirichletBoundary n b ∧ (faceGhostGraph n).Reachable x b := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhost_reaches_boundary n

/--
[vertexGhostPrimitive_superharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexGhostPrimitive_superharmonicOn_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  IsingFiniteWeightedSuperharmonicOn (vertexGhostConductance n) (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexGhostPrimitive_superharmonicOn n hn

/--
[faceGhostPrimitive_subharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceGhostPrimitive_subharmonicOn_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  IsingFiniteWeightedSubharmonicOn (faceGhostConductance n) (faceDirichletBoundary n) (faceGhostPrimitive n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostPrimitive_subharmonicOn n hn

/--
[vertexDirichlet_harmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexDirichlet_harmonicOn_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  IsingFiniteWeightedHarmonicOn (vertexGhostConductance n) (vertexDirichletBoundary n) (vertexDirichlet n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_harmonicOn n hn

/--
[vertexDirichlet_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexDirichlet_boundary_eq
  {n : Nat}
  {x : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hn : 0 < n)
  (hx : vertexDirichletBoundary n x) :
-- imply
  vertexDirichlet n hn x = vertexGhostPrimitive n hn x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_boundary n hn x hx

/--
[faceDirichlet_harmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceDirichlet_harmonicOn_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  IsingFiniteWeightedHarmonicOn (faceGhostConductance n) (faceDirichletBoundary n) (faceDirichlet n hn) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_harmonicOn n hn

/--
[faceDirichlet_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceDirichlet_boundary_eq
  {n : Nat}
  {c : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hn : 0 < n)
  (hc : faceDirichletBoundary n c) :
-- imply
  faceDirichlet n hn c = faceGhostPrimitive n hn c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_boundary n hn c hc

/--
[vertexDirichlet_le_ghostPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexDirichlet_le_ghostPrimitive_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∀ x, vertexDirichlet n hn x ≤ vertexGhostPrimitive n hn x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_le_ghostPrimitive n hn

/--
[faceGhostPrimitive_le_dirichlet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceGhostPrimitive_le_dirichlet_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∀ c, faceGhostPrimitive n hn c ≤ faceDirichlet n hn c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceGhostPrimitive_le_dirichlet n hn

/--
[vertexDirichlet_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexDirichlet_nonneg_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∀ x, 0 ≤ vertexDirichlet n hn x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_nonneg n hn

/--
[vertexDirichlet_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma vertexDirichlet_le_one_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∀ x, vertexDirichlet n hn x ≤ 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexDirichlet_le_one n hn

/--
[faceDirichlet_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceDirichlet_nonneg_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∀ c, 0 ≤ faceDirichlet n hn c := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_nonneg n hn

/--
[faceDirichlet_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma faceDirichlet_le_one_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ∀ c, faceDirichlet n hn c ≤ 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceDirichlet_le_one n hn

/--
[physicalIncidence_dirichlet_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma physicalIncidence_dirichlet_sandwich_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  vertexDirichlet n hn (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) ∧ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) ≤ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤ faceDirichlet n hn (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_dirichlet_sandwich n hn e

/--
[physicalIncidence_close_of_dirichlet_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma physicalIncidence_close_of_dirichlet_close_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
  {target eps : Real}
-- given
  (hn : 0 < n)
  (hvertex : |vertexDirichlet n hn (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - target| ≤ eps)
  (hface : |faceDirichlet n hn (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - target| ≤ eps) :
-- imply
  |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤ eps ∧ |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤ eps := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.physicalIncidence_close_of_dirichlet_close n hn e target eps hvertex hface

/--
[radialPatch_unitRange_and_dirichlet_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma radialPatch_unitRange_and_dirichlet_sandwich_eq
  {n m : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  ((∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧ radialPatchPrimalValue n m hn hm p ≤ 1) ∧ (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧ radialPatchDualValue n m hn hm hm2 q ≤ 1)) ∧ ∀ e : FKIsingSquareInteriorRadialIncidence n hn, vertexDirichlet n hn (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) ∧ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) ≤ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤ faceDirichlet n hn (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatch_unitRange_and_dirichlet_sandwich n m hn hm hm2

/--
[finiteSquare_integratedPrimitive_dirichletComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean)
-/
@[path]
private lemma finiteSquare_integratedPrimitive_dirichletComparison_eq
  {n m : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  ((∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧ radialPatchPrimalValue n m hn hm p ≤ 1) ∧ (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧ radialPatchDualValue n m hn hm hm2 q ≤ 1)) ∧ (∀ x, 0 ≤ vertexDirichlet n hn x ∧ vertexDirichlet n hn x ≤ 1) ∧ (∀ c, 0 ≤ faceDirichlet n hn c ∧ faceDirichlet n hn c ≤ 1) ∧ ∀ e : FKIsingSquareInteriorRadialIncidence n hn, vertexDirichlet n hn (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) ∧ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) ≤ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧ (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤ faceDirichlet n hn (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.finiteSquare_integratedPrimitive_dirichletComparison n m hn hm hm2


-- created on 2026-10-23
