import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPatternSurgery
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[setPattern_primalDualOpenPattern_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma setPattern_primalDualOpenPattern_primal_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {primal : Finset (Sym2 V)}
  {dual : Finset (Sym2 W)}
  {omega : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (he : e ∈ primal) :
-- imply
  setPattern (D.primalDualPatternSupport primal dual) (D.primalDualOpenPattern primal dual) omega e = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.setPattern_primalDualOpenPattern_primal D primal dual omega he

/--
[setPattern_primalDualOpenPattern_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma setPattern_primalDualOpenPattern_dual_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {primal : Finset (Sym2 V)}
  {dual : Finset (Sym2 W)}
  {omega : ConfigSpace (Sym2 V)}
  {e : Sym2 W}
-- given
  (hcompat : Disjoint primal (dual.map D.edgeDual.symm.toEmbedding))
  (he : e ∈ dual) :
-- imply
  dualConfigEquiv D.edgeDual (setPattern (D.primalDualPatternSupport primal dual) (D.primalDualOpenPattern primal dual) omega) e = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.setPattern_primalDualOpenPattern_dual D primal dual hcompat omega he

/--
[exists_primal_dual_open_iff_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma exists_primal_dual_open_iff_disjoint_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {primal : Finset (Sym2 V)}
  {dual : Finset (Sym2 W)} :
-- imply
  (∃ omega : ConfigSpace (Sym2 V), (∀ e ∈ primal, omega e = true) ∧ (∀ e ∈ dual, dualConfigEquiv D.edgeDual omega e = true)) ↔ Disjoint primal (dual.map D.edgeDual.symm.toEmbedding) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_primal_dual_open_iff_disjoint D primal dual

/--
[setPattern_primalDualOpenPattern_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma setPattern_primalDualOpenPattern_of_not_mem_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {primal : Finset (Sym2 V)}
  {dual : Finset (Sym2 W)}
  {omega : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (he : e ∉ D.primalDualPatternSupport primal dual) :
-- imply
  setPattern (D.primalDualPatternSupport primal dual) (D.primalDualOpenPattern primal dual) omega e = omega e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.setPattern_primalDualOpenPattern_of_not_mem D primal dual omega he

/--
[setPattern_primalDualOpenPattern_preserves_walks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma setPattern_primalDualOpenPattern_preserves_walks_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {primal : Finset (Sym2 V)}
  {dual : Finset (Sym2 W)}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {a b : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk a b}
-- given
  (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges → omega s(u, v) = true)
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges → dualConfigEquiv D.edgeDual omega s(u, v) = true)
  (hpavoid : ∀ {u v : V}, s(u, v) ∈ p.edges → s(u, v) ∉ D.primalDualPatternSupport primal dual)
  (hqavoid : ∀ {u v : W}, s(u, v) ∈ q.edges → D.edgeDual.symm s(u, v) ∉ D.primalDualPatternSupport primal dual) :
-- imply
  (∀ {u v : V}, s(u, v) ∈ p.edges → setPattern (D.primalDualPatternSupport primal dual) (D.primalDualOpenPattern primal dual) omega s(u, v) = true) ∧ (∀ {u v : W}, s(u, v) ∈ q.edges → dualConfigEquiv D.edgeDual (setPattern (D.primalDualPatternSupport primal dual) (D.primalDualOpenPattern primal dual) omega) s(u, v) = true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.setPattern_primalDualOpenPattern_preserves_walks D primal dual omega p q hpopen hqopen hpavoid hqavoid

/--
[exists_walk_of_walk_edge_replacements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma exists_walk_of_walk_edge_replacements_eq
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph W}
  {x y : W}
  {q : G.Walk x y}
  {S : Set W}
-- given
  (good : Sym2 W → Prop)
  (hqS : ∀ w ∈ q.support, w ∈ S)
  (hreplace : ∀ {u v : W}, s(u, v) ∈ q.edges → ∃ r : G.Walk u v, (∀ {a b : W}, s(a, b) ∈ r.edges → good s(a, b)) ∧ ∀ w ∈ r.support, w ∈ S) :
-- imply
  ∃ r : G.Walk x y, (∀ {a b : W}, s(a, b) ∈ r.edges → good s(a, b)) ∧ ∀ w ∈ r.support, w ∈ S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_walk_of_walk_edge_replacements q S good hqS hreplace

/--
[setPattern_complementaryDual_walk_of_edge_replacements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma setPattern_complementaryDual_walk_of_edge_replacements_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↑I}
  {omega : ConfigSpace (Sym2 V)}
  {a b : W}
  {q : Pdual.graph.Walk a b}
  {S : Set W}
-- given
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges → dualConfigEquiv D.edgeDual omega s(u, v) = true)
  (hqS : ∀ w ∈ q.support, w ∈ S)
  (hreplace : ∀ {u v : W}, s(u, v) ∈ q.edges → D.edgeDual.symm s(u, v) ∈ I → ∃ r : Pdual.graph.Walk u v, (∀ {c d : W}, s(c, d) ∈ r.edges → dualConfigEquiv D.edgeDual (setPattern I eta omega) s(c, d) = true) ∧ ∀ w ∈ r.support, w ∈ S) :
-- imply
  ∃ r : Pdual.graph.Walk a b, (∀ {u v : W}, s(u, v) ∈ r.edges → dualConfigEquiv D.edgeDual (setPattern I eta omega) s(u, v) = true) ∧ ∀ w ∈ r.support, w ∈ S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.setPattern_complementaryDual_walk_of_edge_replacements D I eta omega q S hqopen hqS hreplace

/--
[measureReal_pos_of_setPattern_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma measureReal_pos_of_setPattern_preimage_eq
  [DecidableEq V]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↑I}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hac : mu.map (setPattern I eta) ≪ mu)
  (hB : MeasurableSet B)
  (hApos : 0 < mu.real A)
  (hsub : A ⊆ setPattern I eta ⁻¹' B) :
-- imply
  0 < mu.real B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.measureReal_pos_of_setPattern_preimage mu I eta hac hB hApos hsub

/--
[measureReal_pos_of_primalDualOpenPattern_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPatternSurgery.lean)
-/
@[path]
private lemma measureReal_pos_of_primalDualOpenPattern_preimage_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {primal : Finset (Sym2 V)}
  {dual : Finset (Sym2 W)}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↑I), mu.map (setPattern I eta) ≪ mu)
  (hB : MeasurableSet B)
  (hApos : 0 < mu.real A)
  (hsub : A ⊆ setPattern (D.primalDualPatternSupport primal dual) (D.primalDualOpenPattern primal dual) ⁻¹' B) :
-- imply
  0 < mu.real B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.measureReal_pos_of_primalDualOpenPattern_preimage D mu hpattern primal dual hB hApos hsub


-- created on 2026-10-23
