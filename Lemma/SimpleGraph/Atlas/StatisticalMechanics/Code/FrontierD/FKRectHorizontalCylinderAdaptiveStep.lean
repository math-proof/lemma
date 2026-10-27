import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderAdaptiveStep
open MeasureTheory SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_boxConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_boxConn_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {x targetX : Fin R.width}
  {psi : ConfigSpace (Sym2 R.Vertex)}
  {P : FKRectHorizontalCylinderUnexploredPlanarization R psi S}
  {p q : Real}
-- given
  (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi S (x, fkRectBottomRow R))
  (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi S (targetX, fkRectTopRow R))
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FKRectHorizontalCylinderAdaptivePairedConnectionEvent R S x targetX psi).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectHorizontalCylinderGraph R) (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectHorizontalCylinderAdaptiveInsideEdges R S psi) psi rho) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 P.radius (P.embedding ⟨(x, fkRectBottomRow R), hsource⟩) (P.embedding ⟨(targetX, fkRectTopRow R), htarget⟩)) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_boxConn R S x targetX psi P hsource htarget hp hp1 hq

/--
[fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_twoPoint_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {x targetX : Fin R.width}
  {psi : ConfigSpace (Sym2 R.Vertex)}
  {P : FKRectHorizontalCylinderUnexploredPlanarization R psi S}
  {p q : Real}
-- given
  (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi S (x, fkRectBottomRow R))
  (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi S (targetX, fkRectTopRow R))
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FKRectHorizontalCylinderAdaptivePairedConnectionEvent R S x targetX psi).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectHorizontalCylinderGraph R) (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectHorizontalCylinderAdaptiveInsideEdges R S psi) psi rho) ≤ FK.infiniteTwoPointReal (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))) (P.embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 (P.embedding ⟨(targetX, fkRectTopRow R), htarget⟩).1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderAdaptivePairedConnectionEvent_condMass_le_twoPoint R S x targetX psi P hsource htarget hp hp1 hq

/--
[fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_adaptiveConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_adaptiveConnection_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
  {x : Fin R.width}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hx : x ∉ S)
  (h : FKRectHorizontalCylinderDistinctPairedWitness R pair (insert x S) rho) :
-- imply
  rho ∈ FKRectHorizontalCylinderAdaptivePairedConnectionEvent R S x (pair x) (fkRectHorizontalCylinderAdaptiveProjection R S rho) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_adaptiveConnection R pair S x hx rho h

/--
[fkRectHorizontalCylinderDistinctPairedWitness_step_of_planarization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_step_of_planarization_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
  {x : Fin R.width}
  {p q a : Real}
-- given
  (hx : x ∉ S)
  (planarize : ∀ psi : ConfigSpace (Sym2 R.Vertex), FKRectHorizontalCylinderDistinctPairedWitness R pair S psi → FKRectHorizontalCylinderUnexploredPlanarization R psi S)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (htwo : ∀ (psi : ConfigSpace (Sym2 R.Vertex)) (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair S psi) (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi S (x, fkRectBottomRow R)) (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi S (pair x, fkRectTopRow R)), FK.infiniteTwoPointReal (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))) ((planarize psi hbase).embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 ((planarize psi hbase).embedding ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair (insert x S) rho} ≤ a * StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_step_of_planarization R pair S x hx planarize hp hp1 hq ha htwo

/--
[fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_step_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {p q a : Real}
  {S : Finset (Fin R.width)}
  {first : Fin R.width}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (step : ∀ (T : Finset (Fin R.width)) (first : Fin R.width), first ∈ T → ∀ (x : Fin R.width), x ∉ T → StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair (insert x T) rho} ≤ a * StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair T rho})
  (hfirst : first ∈ S) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤ a ^ (S.erase first).card := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_step R pair hp hp1 hq ha step S first hfirst

/--
[fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_planarization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_planarization_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {p q a : Real}
  {S : Finset (Fin R.width)}
  {first : Fin R.width}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (planarize : ∀ (T : Finset (Fin R.width)), T.Nonempty → ∀ (psi : ConfigSpace (Sym2 R.Vertex)), FKRectHorizontalCylinderDistinctPairedWitness R pair T psi → FKRectHorizontalCylinderUnexploredPlanarization R psi T)
  (htwo : ∀ (T : Finset (Fin R.width)) (hT : T.Nonempty) (x : Fin R.width) (hx : x ∉ T) (psi : ConfigSpace (Sym2 R.Vertex)) (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi) (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T (x, fkRectBottomRow R)) (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T (pair x, fkRectTopRow R)), FK.infiniteTwoPointReal (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))) ((planarize T hT psi hbase).embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 ((planarize T hT psi hbase).embedding ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
  (hfirst : first ∈ S) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤ a ^ (S.erase first).card := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_planarization R pair hp hp1 hq ha planarize htwo S first hfirst

/--
[fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_planarization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_planarization_eq
  {R : FKRectTorus}
  {p q a : Real}
  {n : Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (planarize : ∀ (pair : Fin R.width → Fin R.width) (T : Finset (Fin R.width)), T.Nonempty → ∀ (psi : ConfigSpace (Sym2 R.Vertex)), FKRectHorizontalCylinderDistinctPairedWitness R pair T psi → FKRectHorizontalCylinderUnexploredPlanarization R psi T)
  (htwo : ∀ (pair : Fin R.width → Fin R.width) (T : Finset (Fin R.width)) (hT : T.Nonempty) (x : Fin R.width) (hx : x ∉ T) (psi : ConfigSpace (Sym2 R.Vertex)) (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi) (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T (x, fkRectBottomRow R)) (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T (pair x, fkRectTopRow R)), FK.infiniteTwoPointReal (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))) ((planarize pair T hT psi hbase).embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 ((planarize pair T hT psi hbase).embedding ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
  (hn : 0 < n) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | n ≤ fkRectHorizontalCylinderCrossingClusterCount R rho} ≤ Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_planarization R hp hp1 hq ha planarize htwo n hn

/--
[fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_twoPoint_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {p q a : Real}
  {S : Finset (Fin R.width)}
  {first : Fin R.width}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (htwo : ∀ (T : Finset (Fin R.width)) (hT : T.Nonempty) (x : Fin R.width) (hx : x ∉ T) (psi : ConfigSpace (Sym2 R.Vertex)) (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi) (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T (x, fkRectBottomRow R)) (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T (pair x, fkRectTopRow R)), FK.infiniteTwoPointReal (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))) ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
  (hfirst : first ∈ S) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤ a ^ (S.erase first).card := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_twoPoint R pair hp hp1 hq ha htwo S first hfirst

/--
[fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_twoPoint_eq
  {R : FKRectTorus}
  {p q a : Real}
  {n : Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (htwo : ∀ (pair : Fin R.width → Fin R.width) (T : Finset (Fin R.width)) (hT : T.Nonempty) (x : Fin R.width) (hx : x ∉ T) (psi : ConfigSpace (Sym2 R.Vertex)) (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi) (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T (x, fkRectBottomRow R)) (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T (pair x, fkRectTopRow R)), FK.infiniteTwoPointReal (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))) ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(pair x, fkRectTopRow R), htarget⟩).1 ≤ a)
  (hn : 0 < n) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) p q) {rho | n ≤ fkRectHorizontalCylinderCrossingClusterCount R rho} ≤ Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTail_le_pow_pred_of_twoPoint R hp hp1 hq ha htwo n hn


-- created on 2026-10-23
