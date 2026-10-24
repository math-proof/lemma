import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSupportForest
open Set SimpleGraph Finset StatMech StatMech.FrontierA


/--
[gnForestData_of_protected_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSupportForest.lean)
-/
@[path]
private lemma gnForestData_of_protected_arms_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {iotaU : Site d → (↑S : Type)}
-- given
  (hGac : G.IsAcyclic)
  (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y → ∃ t1 t2 t3 : (↑S : Type), bc121_Protected omega L R iotaU t1 ∧ bc121_Protected omega L R iotaU t2 ∧ bc121_Protected omega L R iotaU t3 ∧ iotaU y ≠ t1 ∧ iotaU y ≠ t2 ∧ iotaU y ≠ t3 ∧ G.Reachable (iotaU y) t1 ∧ G.Reachable (iotaU y) t2 ∧ G.Reachable (iotaU y) t3 ∧ ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t2 ∧ ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t3 ∧ ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t2 t3)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation omega L z → iotaU y = iotaU z → y = z)
  (hex : ∃ y, y ∈ box d R ∧ bc67_IsGnTrifurcation omega L y) :
-- imply
  bc68_GnForestData omega L R := by
-- proof
  apply StatMech.FrontierA.gnForestData_of_protected_arms omega L R G hGac iotaU harm hinj hex

/--
[coarseTcount_le_boundary_of_protected_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSupportForest.lean)
-/
@[path]
private lemma coarseTcount_le_boundary_of_protected_arms_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {iotaU : Site d → (↑S : Type)}
-- given
  (hGac : G.IsAcyclic)
  (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y → ∃ t1 t2 t3 : (↑S : Type), bc121_Protected omega L R iotaU t1 ∧ bc121_Protected omega L R iotaU t2 ∧ bc121_Protected omega L R iotaU t3 ∧ iotaU y ≠ t1 ∧ iotaU y ≠ t2 ∧ iotaU y ≠ t3 ∧ G.Reachable (iotaU y) t1 ∧ G.Reachable (iotaU y) t2 ∧ G.Reachable (iotaU y) t3 ∧ ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t2 ∧ ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t1 t3 ∧ ¬ (G.deleteIncidenceSet (iotaU y)).Reachable t2 t3)
  (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation omega L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation omega L z → iotaU y = iotaU z → y = z) :
-- imply
  bc61_coarseTcount omega L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.FrontierA.coarseTcount_le_boundary_of_protected_arms omega L R G hGac iotaU harm hinj


-- created on 2026-10-23
