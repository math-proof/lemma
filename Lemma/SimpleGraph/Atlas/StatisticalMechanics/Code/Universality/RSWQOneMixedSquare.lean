import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWQOneMixedSquare.Part4
open Set SimpleGraph MeasureTheory StatMech StatMech.Universality


/--
[rq1_bcWeight_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_bcWeight_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p : ℝ}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  bcWeight G C p 1 omega = edgeProduct G p omega := by
-- proof
  apply StatMech.Universality.rq1_bcWeight_one G C p omega

/--
[rq1_bcProb_one_eq_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_bcProb_one_eq_fkProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p : ℝ}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  bcProb G C p 1 omega = fkProb G p 1 omega := by
-- proof
  apply StatMech.Universality.rq1_bcProb_one_eq_fkProb G C p omega

/--
[rq1_bcEventMass_one_eq_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_bcEventMass_one_eq_bernoulli_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) (G.edgeFinset : Set (Sym2 V))) :
-- imply
  ∑ omega : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p 1 omega = (bernoulliProductMeasure (E := Sym2 V) ⟨p, hp.le⟩ (by exact_mod_cast hp1.le)).real A := by
-- proof
  apply StatMech.Universality.rq1_bcEventMass_one_eq_bernoulli G C hp hp1 A hA

/--
[rq1_finiteMixedSquareEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_finiteMixedSquareEvent_dependsOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ} :
-- imply
  _root_.DependsOn ((rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ))) ((boxGraph 2 n).edgeFinset : Set (Sym2 (boxVerts 2 n))) := by
-- proof
  apply StatMech.Universality.rq1_finiteMixedSquareEvent_dependsOn G n

/--
[rq1_finiteMixedSquareEvent_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_finiteMixedSquareEvent_preimage_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ} :
-- imply
  boxRestrict 2 n ⁻¹' rq1_finiteMixedSquareEvent n = horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ) := by
-- proof
  apply StatMech.Universality.rq1_finiteMixedSquareEvent_preimage G n

/--
[rq1_centeredSquare_crossing_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_centeredSquare_crossing_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
-- proof
  apply StatMech.Universality.rq1_centeredSquare_crossing_half G n hn

/--
[rq1_finiteBernoulli_mixedSquare_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_finiteBernoulli_mixedSquare_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ} :
-- imply
  (bernoulliProductMeasure (E := Sym2 (boxVerts 2 n)) (2⁻¹ : ℝ≥0) half_le_one).real (rq1_finiteMixedSquareEvent n) = rba_selfDualMeasure.real (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
-- proof
  apply StatMech.Universality.rq1_finiteBernoulli_mixedSquare_eq G n

/--
[rq1_bcMixedSquare_crossing_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_bcMixedSquare_crossing_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {C : SimpleGraph (boxVerts 2 n)}
  [DecidableRel C.Adj]
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 2 ≤ ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)), (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta * bcProb (boxGraph 2 n) C ((1 : ℝ) / 2) 1 eta := by
-- proof
  apply StatMech.Universality.rq1_bcMixedSquare_crossing_half G n hn C

/--
[rq1_mixedSquareWiring_bottom_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquareWiring_bottom_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {x y : boxVerts 2 n}
-- given
  (hne : x ≠ y)
  (hx : (x : Site 2) 1 = -(n : ℤ))
  (hy : (y : Site 2) 1 = -(n : ℤ)) :
-- imply
  (rq1_mixedSquareWiring n).Adj x y := by
-- proof
  apply StatMech.Universality.rq1_mixedSquareWiring_bottom_adj G hne hx hy

/--
[rq1_mixedSquareWiring_top_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquareWiring_top_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {x y : boxVerts 2 n}
-- given
  (hne : x ≠ y)
  (hx : (x : Site 2) 1 = (n : ℤ))
  (hy : (y : Site 2) 1 = (n : ℤ)) :
-- imply
  (rq1_mixedSquareWiring n).Adj x y := by
-- proof
  apply StatMech.Universality.rq1_mixedSquareWiring_top_adj G hne hx hy

/--
[rq1_mixedSquareWiring_bottom_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquareWiring_bottom_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {x y : boxVerts 2 n}
-- given
  (hx : (x : Site 2) 1 = -(n : ℤ))
  (hy : (y : Site 2) 1 = -(n : ℤ)) :
-- imply
  (rq1_mixedSquareWiring n).Reachable x y := by
-- proof
  apply StatMech.Universality.rq1_mixedSquareWiring_bottom_reachable G hx hy

/--
[rq1_mixedSquareWiring_top_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquareWiring_top_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {x y : boxVerts 2 n}
-- given
  (hx : (x : Site 2) 1 = (n : ℤ))
  (hy : (y : Site 2) 1 = (n : ℤ)) :
-- imply
  (rq1_mixedSquareWiring n).Reachable x y := by
-- proof
  apply StatMech.Universality.rq1_mixedSquareWiring_top_reachable G hx hy

/--
[rq1_mixedSquareWiring_reachable_preserves_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquareWiring_reachable_preserves_bottom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {x y : boxVerts 2 n}
-- given
  (hn : 0 < n)
  (hx : (x : Site 2) 1 = -(n : ℤ))
  (hxy : (rq1_mixedSquareWiring n).Reachable x y) :
-- imply
  (y : Site 2) 1 = -(n : ℤ) := by
-- proof
  apply StatMech.Universality.rq1_mixedSquareWiring_reachable_preserves_bottom G hn hx hxy

/--
[rq1_mixedSquareWiring_top_bottom_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquareWiring_top_bottom_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {x y : boxVerts 2 n}
-- given
  (hn : 0 < n)
  (hx : (x : Site 2) 1 = -(n : ℤ))
  (hy : (y : Site 2) 1 = (n : ℤ)) :
-- imply
  ¬ (rq1_mixedSquareWiring n).Reachable x y := by
-- proof
  apply StatMech.Universality.rq1_mixedSquareWiring_top_bottom_not_reachable G hn hx hy

/--
[rq1_mixedSquareWiring_top_bottom_not_joined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquareWiring_top_bottom_not_joined_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {x y : boxVerts 2 n}
-- given
  (hn : 0 < n)
  (hx : (x : Site 2) 1 = -(n : ℤ))
  (hy : (y : Site 2) 1 = (n : ℤ)) :
-- imply
  ¬ (rq1_mixedSquareWiring n).Adj x y := by
-- proof
  apply StatMech.Universality.rq1_mixedSquareWiring_top_bottom_not_joined G hn hx hy

/--
[rq1_mixedSquare_crossing_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_mixedSquare_crossing_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / (1 + 1 ^ 2) ≤ ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)), (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta * bcProb (boxGraph 2 n) (rq1_mixedSquareWiring n) ((1 : ℝ) / 2) 1 eta := by
-- proof
  apply StatMech.Universality.rq1_mixedSquare_crossing_lower_bound G n hn

/--
[rq1_wiredSquare_crossing_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_wiredSquare_crossing_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 2 ≤ ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)), (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta * wiredFkProb (boxGraph 2 n) (boxBoundary 2 n) ((1 : ℝ) / 2) 1 eta := by
-- proof
  apply StatMech.Universality.rq1_wiredSquare_crossing_half G n hn

/--
[rq1_stripDualReflectedSquare_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_stripDualReflectedSquare_law_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ} :
-- imply
  rba_selfDualMeasure.real (rq1_stripDualReflectedSquareEvent n) = rba_selfDualMeasure.real (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
-- proof
  apply StatMech.Universality.rq1_stripDualReflectedSquare_law G n

/--
[rq1_stripDualReflectedSquare_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean)
-/
@[path]
private lemma rq1_stripDualReflectedSquare_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rq1_stripDualReflectedSquareEvent n) := by
-- proof
  apply StatMech.Universality.rq1_stripDualReflectedSquare_half G n hn


-- created on 2026-10-23
