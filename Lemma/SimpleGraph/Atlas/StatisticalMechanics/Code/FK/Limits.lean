import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.Limits
open MeasureTheory StatMech.Lattice SimpleGraph StatMech StatMech.FK


/--
[openSub_eq_openGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma openSub_eq_openGraph_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  openSub G ω = StatMech.Lattice.openGraph G ω := by
-- proof
  apply StatMech.FK.openSub_eq_openGraph G bdry ω

/--
[numClusters_eq_numClustersFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma numClusters_eq_numClustersFree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  numClusters G ω = numClustersFree G ω := by
-- proof
  apply StatMech.FK.numClusters_eq_numClustersFree G bdry ω

/--
[openGraph_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma openGraph_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  StatMech.Lattice.openGraph G (a ⊓ b) = StatMech.Lattice.openGraph G a ⊓ StatMech.Lattice.openGraph G b := by
-- proof
  apply StatMech.FK.openGraph_inf G bdry a b

/--
[openGraph_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma openGraph_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  StatMech.Lattice.openGraph G (a ⊔ b) = StatMech.Lattice.openGraph G a ⊔ StatMech.Lattice.openGraph G b := by
-- proof
  apply StatMech.FK.openGraph_sup G bdry a b

/--
[mixed_supermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma mixed_supermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  numClusters G a + numClustersWired G bdry b ≤ numClusters G (a ⊓ b) + numClustersWired G bdry (a ⊔ b) := by
-- proof
  apply StatMech.FK.mixed_supermodular G bdry a b

/--
[freeWiredWeight_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma freeWiredWeight_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  fkWeight G p q a * wiredFkWeight G bdry p q b ≤ fkWeight G p q (a ⊓ b) * wiredFkWeight G bdry p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.freeWiredWeight_cross G bdry hp hp1 hq a b

/--
[freeWiredProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma freeWiredProb_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  fkProb G p q a * wiredFkProb G bdry p q b ≤ fkProb G p q (a ⊓ b) * wiredFkProb G bdry p q (a ⊔ b) := by
-- proof
  apply StatMech.FK.freeWiredProb_cross G bdry hp hp1 hq a b

/--
[fkProb_le_wiredFkProb_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma fkProb_le_wiredFkProb_increasing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω := by
-- proof
  apply StatMech.FK.fkProb_le_wiredFkProb_increasing G bdry hp hp1 hq hA

/--
[monotone_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma monotone_extendEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n : ℕ}
-- given
  (bdry : V → Prop) :
-- imply
  Monotone (extendEdge d n) := by
-- proof
  apply StatMech.FK.monotone_extendEdge G bdry d n

/--
[isIncreasing_preimage_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma isIncreasing_preimage_extendEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n : ℕ}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (bdry : V → Prop)
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (extendEdge d n ⁻¹' A) := by
-- proof
  apply StatMech.FK.isIncreasing_preimage_extendEdge G bdry d n hA

/--
[fkPMF_toMeasure_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma fkPMF_toMeasure_toReal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ((fkPMF (boxGraph d n) hp hp1 hq).toMeasure S).toReal = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), S.indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d n) p q ω := by
-- proof
  apply StatMech.FK.fkPMF_toMeasure_toReal G bdry d n hp hp1 hq S

/--
[wiredFkPMF_toMeasure_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma wiredFkPMF_toMeasure_toReal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure S).toReal = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), S.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.wiredFkPMF_toMeasure_toReal G bdry d n hp hp1 hq S

/--
[freeFiniteMeasure_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Limits.lean)
-/
@[path]
private lemma freeFiniteMeasure_dominated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n : ℕ}
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (freeFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) ≼ (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_dominated G bdry d n hp hp1 hq


-- created on 2026-10-23
