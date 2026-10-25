import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
open MeasureTheory Filter Topology Set SimpleGraph StatMech StatMech.FK


/--
[openGraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma openGraph_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (h : a ≤ b) :
-- imply
  openGraph G a ≤ openGraph G b := by
-- proof
  apply StatMech.FK.openGraph_mono G bdry h

/--
[wiredGraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma wiredGraph_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (h : a ≤ b) :
-- imply
  wiredGraph G bdry a ≤ wiredGraph G bdry b := by
-- proof
  apply StatMech.FK.wiredGraph_mono G bdry h

/--
[numClustersWired_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma numClustersWired_antitone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {a b : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (h : a ≤ b) :
-- imply
  numClustersWired G bdry b ≤ numClustersWired G bdry a := by
-- proof
  apply StatMech.FK.numClustersWired_antitone G bdry h

/--
[wiredFkWeight_edgeProduct_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma wiredFkWeight_edgeProduct_cross_eq
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
  wiredFkWeight G bdry p q a * edgeProduct G p b ≤ wiredFkWeight G bdry p q (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
-- proof
  apply StatMech.FK.wiredFkWeight_edgeProduct_cross G bdry hp hp1 hq a b

/--
[wiredFkProb_fkProbOne_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma wiredFkProb_fkProbOne_cross_eq
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
  wiredFkProb G bdry p q a * fkProb G p 1 b ≤ wiredFkProb G bdry p q (a ⊓ b) * fkProb G p 1 (a ⊔ b) := by
-- proof
  apply StatMech.FK.wiredFkProb_fkProbOne_cross G bdry hp hp1 hq a b

/--
[wiredFkProb_le_fkProbOne_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma wiredFkProb_le_fkProbOne_increasing_eq
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
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p 1 ω := by
-- proof
  apply StatMech.FK.wiredFkProb_le_fkProbOne_increasing G bdry hp hp1 hq hA

/--
[sum_prod_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma sum_prod_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype ι]
  [DecidableEq ι]
  {s : Finset ι}
-- given
  (bdry : V → Prop)
  (h : ι → Bool → ℝ) :
-- imply
  ∑ ω : ι → Bool, ∏ e ∈ s, h e (ω e) = 2 ^ (Fintype.card ι - s.card) * ∏ e ∈ s, (∑ b : Bool, h e b) := by
-- proof
  apply StatMech.FK.sum_prod_factor G bdry s h

/--
[fkProbOne_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma fkProbOne_cylinder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hF : F ⊆ G.edgeFinset) :
-- imply
  ∑ ω : ConfigSpace (Sym2 V), (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb G p 1 ω = p ^ F.card := by
-- proof
  apply StatMech.FK.fkProbOne_cylinder G bdry hp hp1 F hF

/--
[isClopen_singleOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma isClopen_singleOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {e : Sym2 (Site d)}
-- given
  (bdry : V → Prop) :
-- imply
  IsClopen {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
-- proof
  apply StatMech.FK.isClopen_singleOpen G bdry e

/--
[isClopen_wordEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma isClopen_wordEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {m : ℕ}
-- given
  (bdry : V → Prop) :
-- imply
  IsClopen (wordEvent g m) := by
-- proof
  apply StatMech.FK.isClopen_wordEvent G bdry g m

/--
[isIncreasing_wordEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma isIncreasing_wordEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {g : ℕ → Fin d × Bool}
  {m : ℕ}
-- given
  (bdry : V → Prop) :
-- imply
  IsIncreasing (wordEvent g m) := by
-- proof
  apply StatMech.FK.isIncreasing_wordEvent G bdry g m

/--
[isClopen_fkExistsOpenWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma isClopen_fkExistsOpenWalk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {m : ℕ}
-- given
  (bdry : V → Prop)
  (hd : 0 < d) :
-- imply
  IsClopen (fkExistsOpenWalk d m hd) := by
-- proof
  apply StatMech.FK.isClopen_fkExistsOpenWalk G bdry m hd

/--
[isIncreasing_fkExistsOpenWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma isIncreasing_fkExistsOpenWalk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {m : ℕ}
-- given
  (bdry : V → Prop)
  (hd : 0 < d) :
-- imply
  IsIncreasing (fkExistsOpenWalk d m hd) := by
-- proof
  apply StatMech.FK.isIncreasing_fkExistsOpenWalk G bdry m hd

/--
[percolationEvent_subset_fkExistsOpenWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma percolationEvent_subset_fkExistsOpenWalk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {m : ℕ}
-- given
  (bdry : V → Prop)
  (hd : 0 < d) :
-- imply
  percolationEvent d ⊆ fkExistsOpenWalk d m hd := by
-- proof
  apply StatMech.FK.percolationEvent_subset_fkExistsOpenWalk G bdry hd m

/--
[extendEdge_eq_of_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma extendEdge_eq_of_range_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {n : ℕ}
  {be : Sym2 (boxVerts d n)}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
-- given
  (bdry : V → Prop) :
-- imply
  extendEdge d n ω (edgeIncl d n be) = ω be := by
-- proof
  apply StatMech.FK.extendEdge_eq_of_range G bdry n be ω

/--
[range_of_extendEdge_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma range_of_extendEdge_true_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {e : Sym2 (Site d)}
-- given
  (bdry : V → Prop)
  (h : extendEdge d n ω e = true) :
-- imply
  e ∈ Set.range (edgeIncl d n) := by
-- proof
  apply StatMech.FK.range_of_extendEdge_true G bdry n ω e h

/--
[boxEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma boxEdge_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {n : ℕ}
  {be : Sym2 (boxVerts d n)}
  {x y : Site d}
-- given
  (bdry : V → Prop)
  (hadj : (hypercubicLattice d).Adj x y)
  (heq : edgeIncl d n be = s(x, y)) :
-- imply
  be ∈ (boxGraph d n).edgeFinset := by
-- proof
  apply StatMech.FK.boxEdge_mem G bdry n be x y hadj heq

/--
[exists_boxF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma exists_boxF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {n m : ℕ}
  {g : ℕ → Fin d × Bool}
-- given
  (bdry : V → Prop)
  (hg : goodWord g m)
  (hrange : ∀ k ∈ Finset.range m, edgeOf g k ∈ Set.range (edgeIncl d n)) :
-- imply
  ∃ F : Finset (Sym2 (boxVerts d n)), F ⊆ (boxGraph d n).edgeFinset ∧ F.card = m ∧ (extendEdge d n ⁻¹' wordEvent g m ⊆ {ω | ∀ be ∈ F, ω be = true}) := by
-- proof
  apply StatMech.FK.exists_boxF G bdry n m g hg hrange

/--
[perWord_box_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma perWord_box_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {n m : ℕ}
  {g : ℕ → Fin d × Bool}
  {p : ℝ}
-- given
  (bdry : V → Prop)
  (hg : goodWord g m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (extendEdge d n ⁻¹' wordEvent g m).indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d n) p 1 ω ≤ p ^ m := by
-- proof
  apply StatMech.FK.perWord_box_bound G bdry n m g hg hp hp1

/--
[wiredFiniteMeasure_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hA : MeasurableSet A) :
-- imply
  (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real A = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (extendEdge d n ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_real_eq G bdry n hp hp1 hq A hA

/--
[wiredFiniteMeasure_fkExistsOpenWalk_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma wiredFiniteMeasure_fkExistsOpenWalk_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {n m : ℕ}
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hd : 0 < d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (fkExistsOpenWalk d m hd) ≤ ((2 * d : ℝ) * p) ^ m := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_fkExistsOpenWalk_le G bdry n m hd hp hp1 hq

/--
[fkTheta_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma fkTheta_le_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {p q : ℝ}
  {m : ℕ}
-- given
  (bdry : V → Prop)
  (hd : 0 < d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) ≤ ((2 * d : ℝ) * p) ^ m := by
-- proof
  apply StatMech.FK.fkTheta_le_pow G bdry hd hp hp1 hq m

/--
[fkTheta_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma fkTheta_eq_zero_of_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hd : 0 < d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hsmall : (2 * d : ℝ) * p < 1) :
-- imply
  fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 := by
-- proof
  apply StatMech.FK.fkTheta_eq_zero_of_lt G bdry hd hp hp1 hq hsmall

/--
[fkSubcriticalSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma fkSubcriticalSet_bddAbove_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {d : ℕ}
  {q : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  BddAbove (fkSubcriticalSet d q) := by
-- proof
  apply StatMech.FK.fkSubcriticalSet_bddAbove G bdry d q

/--
[le_fkPc_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma le_fkPc_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {d : ℕ}
  {q p : ℝ}
-- given
  (bdry : V → Prop)
  (hp : p ∈ fkSubcriticalSet d q) :
-- imply
  p ≤ fkPc d q := by
-- proof
  apply StatMech.FK.le_fkPc_of_mem G bdry hp

/--
[fkPc_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma fkPc_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {q : ℝ}
-- given
  (bdry : V → Prop)
  (hd : 0 < d)
  (hq : 1 ≤ q) :
-- imply
  0 < fkPc d q := by
-- proof
  apply StatMech.FK.fkPc_pos G bdry hd hq

/--
[fkPc_pos_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean)
-/
@[path]
private lemma fkPc_pos_of_two_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {q : ℝ}
-- given
  (bdry : V → Prop)
  (hd : 2 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  0 < fkPc d q := by
-- proof
  apply StatMech.FK.fkPc_pos_of_two_le G bdry hd hq


-- created on 2026-10-23
