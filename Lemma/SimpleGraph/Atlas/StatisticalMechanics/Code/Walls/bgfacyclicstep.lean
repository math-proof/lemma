import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bgfacyclicstep
open Set SimpleGraph Finset StatMech StatMech.Walls


/--
[bgf_acyclic_of_regionSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_acyclic_of_regionSep_eq
  {σ : V → Type*}
  {G : SimpleGraph V}
  {region : (t : V) → V → σ t}
-- given
  (H1 : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → region t a ≠ region t b)
  (H2 : ∀ t a b (w : G.Walk a b), t ∉ w.support → region t a = region t b) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bgf_acyclic_of_regionSep G region H1 H2

/--
[bgf_walkReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_walkReach_eq
  {G : SimpleGraph V}
  {H : V → SimpleGraph V}
  {t : V}
-- given
  (hlift : ∀ a b, G.Adj a b → t ≠ a → t ≠ b → (H t).Reachable a b) :
-- imply
  ∀ a b (w : G.Walk a b), t ∉ w.support → (H t).Reachable a b := by
-- proof
  apply StatMech.Walls.bgf_walkReach G H t hlift

/--
[bgf_acyclic_of_reachSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_acyclic_of_reachSep_eq
  {G : SimpleGraph V}
  {H : V → SimpleGraph V}
-- given
  (H1 : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (H t).Reachable a b)
  (H2 : ∀ t a b (w : G.Walk a b), t ∉ w.support → (H t).Reachable a b) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bgf_acyclic_of_reachSep G H H1 H2

/--
[bgf_acyclic_of_edgeLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_acyclic_of_edgeLift_eq
  {G : SimpleGraph V}
  {H : V → SimpleGraph V}
-- given
  (Hcut : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (H t).Reachable a b)
  (Hlift : ∀ t a b, G.Adj a b → t ≠ a → t ≠ b → (H t).Reachable a b) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bgf_acyclic_of_edgeLift G H Hcut Hlift

/--
[bgf_step3_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_step3_witness_eq :
-- imply
  (SimpleGraph.fromEdgeSet {s((0 : Fin 4), 1), s((0 : Fin 4), 2), s((0 : Fin 4), 3)}).IsAcyclic := by
-- proof
  apply StatMech.Walls.bgf_step3_witness

/--
[bgf_bc67_walkReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_bc67_walkReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {G : SimpleGraph V}
  {embed : V → Site d}
  {t : V}
-- given
  (hlift : ∀ a b, G.Adj a b → t ≠ a → t ≠ b → (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) :
-- imply
  ∀ a b (w : G.Walk a b), t ∉ w.support → (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b) := by
-- proof
  apply StatMech.Walls.bgf_bc67_walkReach ω L G embed t hlift

/--
[bgf_bc67_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_bc67_acyclic_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {G : SimpleGraph V}
  {embed : V → Site d}
-- given
  (Hcut : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b))
  (Hlift : ∀ t a b, G.Adj a b → t ≠ a → t ≠ b → (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bgf_bc67_acyclic ω L G embed Hcut Hlift

/--
[bgf_acyclicStep_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfacyclicstep.lean)
-/
@[path]
private lemma bgf_acyclicStep_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} {σ : V → Type} (G : SimpleGraph V) (region : (t : V) → V → σ t), (∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → region t a ≠ region t b) → (∀ t a b (w : G.Walk a b), t ∉ w.support → region t a = region t b) → G.IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {V : Type} (G : SimpleGraph V) (embed : V → Site d), (∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) → (∀ t a b, G.Adj a b → t ≠ a → t ≠ b → (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) → G.IsAcyclic) ∧ ((SimpleGraph.fromEdgeSet {s((0 : Fin 4), 1), s((0 : Fin 4), 2), s((0 : Fin 4), 3)}).IsAcyclic) := by
-- proof
  apply StatMech.Walls.bgf_acyclicStep_status


-- created on 2026-10-23
