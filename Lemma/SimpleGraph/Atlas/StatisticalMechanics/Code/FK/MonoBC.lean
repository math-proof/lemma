import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
open SimpleGraph StatMech StatMech.FK


/--
[numClustersBC_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma numClustersBC_bot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClustersBC G (⊥ : SimpleGraph V) ω = numClusters G ω := by
-- proof
  apply StatMech.FK.numClustersBC_bot G ω

/--
[numClustersBC_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma numClustersBC_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  numClustersBC G (StatMech.Lattice.boundaryCliqueGraph bdry) ω = StatMech.Lattice.numClustersWired G bdry ω := by
-- proof
  apply StatMech.FK.numClustersBC_boundaryClique G bdry ω

/--
[mixed_supermodular_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma mixed_supermodular_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hCC' : C ≤ C') :
-- imply
  numClustersBC G C a + numClustersBC G C' b ≤ numClustersBC G C (a ⊓ b) + numClustersBC G C' (a ⊔ b) := by
-- proof
  apply StatMech.FK.mixed_supermodular_bc G bdry C C' hCC' a b

/--
[bcWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < bcWeight G C p q ω := by
-- proof
  apply StatMech.FK.bcWeight_pos G bdry C hp hp1 hq ω

/--
[bcWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ bcWeight G C p q ω := by
-- proof
  apply StatMech.FK.bcWeight_nonneg G bdry C hp hp1 hq ω

/--
[bcZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < bcZ G C p q := by
-- proof
  apply StatMech.FK.bcZ_pos G bdry C hp hp1 hq

/--
[bcZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  bcZ G C p q ≠ 0 := by
-- proof
  apply StatMech.FK.bcZ_ne_zero G bdry C hp hp1 hq

/--
[bcProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ bcProb G C p q ω := by
-- proof
  apply StatMech.FK.bcProb_nonneg G bdry C hp hp1 hq ω

/--
[bcProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω : ConfigSpace (Sym2 V), bcProb G C p q ω = 1 := by
-- proof
  apply StatMech.FK.bcProb_sum_eq_one G bdry C hp hp1 hq

/--
[bcWeight_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcWeight_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  bcWeight G C p q a * bcWeight G C' p q b ≤ bcWeight G C p q (a ⊓ b) * bcWeight G C' p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcWeight_cross G bdry C C' hCC' hp hp1 hq a b

/--
[bcProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcProb_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  bcProb G C p q a * bcProb G C' p q b ≤ bcProb G C p q (a ⊓ b) * bcProb G C' p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcProb_cross G bdry C C' hCC' hp hp1 hq a b

/--
[bcProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcProb_FKGLatticeCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  FKGLatticeCondition (fun ω => bcProb G C p q ω) := by
-- proof
  apply StatMech.FK.bcProb_FKGLatticeCondition G bdry C hp hp1 hq

/--
[bcProb_positively_associated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcProb_positively_associated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ ω, bcProb G C p q ω * f ω) * (∑ ω, bcProb G C p q ω * g ω) ≤ ∑ ω, bcProb G C p q ω * (f ω * g ω) := by
-- proof
  apply StatMech.FK.bcProb_positively_associated G bdry C hp hp1 hq hf hg

/--
[bcProb_positively_associated_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcProb_positively_associated_events_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (∑ ω, bcProb G C p q ω * A.indicator (fun _ => (1 : ℝ)) ω) * (∑ ω, bcProb G C p q ω * B.indicator (fun _ => (1 : ℝ)) ω) ≤ ∑ ω, bcProb G C p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.FK.bcProb_positively_associated_events G bdry C hp hp1 hq hA hB

/--
[bcProb_mono_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean)
-/
@[path]
private lemma bcProb_mono_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C' p q ω := by
-- proof
  apply StatMech.FK.bcProb_mono_bc G bdry C C' hCC' hp hp1 hq hA


-- created on 2026-10-23
