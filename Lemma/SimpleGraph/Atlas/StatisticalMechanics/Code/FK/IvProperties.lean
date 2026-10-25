import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.IvProperties
open SimpleGraph StatMech StatMech.FK


/--
[bc_le_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvProperties.lean)
-/
@[path]
private lemma bc_le_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
-- given
  (bdry : V → Prop)
  (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y) :
-- imply
  C ≤ StatMech.Lattice.boundaryCliqueGraph bdry := by
-- proof
  apply StatMech.FK.bc_le_boundaryClique G bdry C hC

/--
[bcProb_bot_eq_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvProperties.lean)
-/
@[path]
private lemma bcProb_bot_eq_fkProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  bcProb G (⊥ : SimpleGraph V) p q ω = fkProb G p q ω := by
-- proof
  apply StatMech.FK.bcProb_bot_eq_fkProb G bdry p q ω

/--
[bcProb_clique_eq_wiredFkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvProperties.lean)
-/
@[path]
private lemma bcProb_clique_eq_wiredFkProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω = wiredFkProb G bdry p q ω := by
-- proof
  apply StatMech.FK.bcProb_clique_eq_wiredFkProb G bdry p q ω

/--
[bcProb_free_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvProperties.lean)
-/
@[path]
private lemma bcProb_free_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω := by
-- proof
  apply StatMech.FK.bcProb_free_le G bdry C hp hp1 hq hA

/--
[bcProb_le_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvProperties.lean)
-/
@[path]
private lemma bcProb_le_wired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω := by
-- proof
  apply StatMech.FK.bcProb_le_wired G bdry C hC hp hp1 hq hA

/--
[bcProb_extremality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvProperties.lean)
-/
@[path]
private lemma bcProb_extremality_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (⊥ : SimpleGraph V) p q ω) ≤ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G (StatMech.Lattice.boundaryCliqueGraph bdry) p q ω := by
-- proof
  apply StatMech.FK.bcProb_extremality G bdry C hC hp hp1 hq hA

/--
[fkProb_le_bcProb_le_wiredFkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvProperties.lean)
-/
@[path]
private lemma fkProb_le_bcProb_le_wiredFkProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hC : ∀ x y, C.Adj x y → bdry x ∧ bdry y)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω) ≤ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ∧ (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω := by
-- proof
  apply StatMech.FK.fkProb_le_bcProb_le_wiredFkProb G bdry C hC hp hp1 hq hA


-- created on 2026-10-23
