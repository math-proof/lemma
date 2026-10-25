import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
open StatMech StatMech.FK


/--
[hasDerivAt_edgeFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma hasDerivAt_edgeFactor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
  {p : ℝ} :
-- imply
  HasDerivAt (fun p => if ω e then p else 1 - p) (if ω e then (1 : ℝ) else -1) p := by
-- proof
  apply StatMech.FK.hasDerivAt_edgeFactor G ω e p

/--
[hasDerivAt_edgeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma hasDerivAt_edgeProduct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)}
  {p : ℝ} :
-- imply
  HasDerivAt (fun p => edgeProduct G p ω) (∑ e ∈ G.edgeFinset, edgeProductOff G p e ω * (if ω e then (1 : ℝ) else -1)) p := by
-- proof
  apply StatMech.FK.hasDerivAt_edgeProduct G ω p

/--
[edgeProduct_eq_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma edgeProduct_eq_off_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∈ G.edgeFinset) :
-- imply
  edgeProduct G p ω = edgeProductOff G p e ω * (if ω e then p else 1 - p) := by
-- proof
  apply StatMech.FK.edgeProduct_eq_off G p e ω he

/--
[edgeProductOff_term](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma edgeProductOff_term_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (he : e ∈ G.edgeFinset) :
-- imply
  edgeProductOff G p e ω * (if ω e then (1 : ℝ) else -1) = edgeProduct G p ω * ((coord e ω - p) / (p * (1 - p))) := by
-- proof
  apply StatMech.FK.edgeProductOff_term G p hp hp1 e ω he

/--
[sum_coord_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma sum_coord_sub_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  ∑ e ∈ G.edgeFinset, (coord e ω - p) = openEdgeCount G ω - p * (G.edgeFinset.card : ℝ) := by
-- proof
  apply StatMech.FK.sum_coord_sub G p ω

/--
[hasDerivAt_edgeProduct_clean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma hasDerivAt_edgeProduct_clean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun p => edgeProduct G p ω) (edgeProduct G p ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_edgeProduct_clean G hp hp1 ω

/--
[hasDerivAt_fkWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma hasDerivAt_fkWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun p => fkWeight G p q ω) (fkWeight G p q ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_fkWeight G hp hp1 q ω

/--
[fkNumer_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkNumer_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  fkNumer G p q (fun _ => 1) = fkZ G p q := by
-- proof
  apply StatMech.FK.fkNumer_one G p q

/--
[hasDerivAt_fkNumer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma hasDerivAt_fkNumer_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun p => fkNumer G p q g) ((∑ ω : ConfigSpace (Sym2 V), g ω * (fkWeight G p q ω * (∑ e ∈ G.edgeFinset, (coord e ω - p)))) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_fkNumer G hp hp1 q g

/--
[fkMean_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkMean_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  fkMean G p q g = fkNumer G p q g / fkZ G p q := by
-- proof
  apply StatMech.FK.fkMean_eq_div G p q g

/--
[fkMean_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkMean_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (g h : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  fkMean G p q (fun ω => g ω + h ω) = fkMean G p q g + fkMean G p q h := by
-- proof
  apply StatMech.FK.fkMean_add G p q g h

/--
[fkMean_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkMean_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {s : Finset ι}
  {g : ι → ConfigSpace (Sym2 V) → ℝ} :
-- imply
  fkMean G p q (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, fkMean G p q (g i) := by
-- proof
  apply StatMech.FK.fkMean_sum G p q s g

/--
[fkMean_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkMean_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {c : ℝ}
-- given
  (hZ : fkZ G p q ≠ 0) :
-- imply
  fkMean G p q (fun _ => c) = c := by
-- proof
  apply StatMech.FK.fkMean_const G p q hZ

/--
[fkMean_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkMean_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {c : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  fkMean G p q (fun ω => c * g ω) = c * fkMean G p q g := by
-- proof
  apply StatMech.FK.fkMean_const_mul G p q c g

/--
[fkCov_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkCov_add_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (f g h : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  fkCov G p q f (fun ω => g ω + h ω) = fkCov G p q f g + fkCov G p q f h := by
-- proof
  apply StatMech.FK.fkCov_add_right G p q f g h

/--
[fkCov_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkCov_sum_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {s : Finset ι}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {g : ι → ConfigSpace (Sym2 V) → ℝ} :
-- imply
  fkCov G p q f (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, fkCov G p q f (g i) := by
-- proof
  apply StatMech.FK.fkCov_sum_right G p q s f g

/--
[fkCov_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkCov_sub_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ}
  {c : ℝ}
-- given
  (hZ : fkZ G p q ≠ 0) :
-- imply
  fkCov G p q f (fun ω => g ω - c) = fkCov G p q f g := by
-- proof
  apply StatMech.FK.fkCov_sub_const G p q f g hZ

/--
[fkCov_centeredCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma fkCov_centeredCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hZ : fkZ G p q ≠ 0) :
-- imply
  fkCov G p q g (fun ω => ∑ e ∈ G.edgeFinset, (coord e ω - p)) = ∑ e ∈ G.edgeFinset, fkCov G p q g (coord e) := by
-- proof
  apply StatMech.FK.fkCov_centeredCount G p q hZ g

/--
[hasDerivAt_fkMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma hasDerivAt_fkMean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun p => fkMean G p q g) ((∑ e ∈ G.edgeFinset, fkCov G p q g (coord e)) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_fkMean G hp hp1 hq g

/--
[deriv_fkMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma deriv_fkMean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  deriv (fun p => fkMean G p q g) p = (∑ e ∈ G.edgeFinset, fkCov G p q g (coord e)) / (p * (1 - p)) := by
-- proof
  apply StatMech.FK.deriv_fkMean G hp hp1 hq g

/--
[hasDerivAt_fkProbOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma hasDerivAt_fkProbOf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun p => fkProbOf G p q A) ((∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e)) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_fkProbOf G hp hp1 hq A

/--
[deriv_fkProbOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma deriv_fkProbOf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  deriv (fun p => fkProbOf G p q A) p = (∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e)) / (p * (1 - p)) := by
-- proof
  apply StatMech.FK.deriv_fkProbOf G hp hp1 hq A

/--
[russoPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma russoPrefactor_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < russoPrefactor p := by
-- proof
  apply StatMech.FK.russoPrefactor_pos G hp hp1

/--
[russo_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean)
-/
@[path]
private lemma russo_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  russoPrefactor p * (∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e)) ≤ deriv (fun p => fkProbOf G p q A) p := by
-- proof
  apply StatMech.FK.russo_bound G hp hp1 hq A


-- created on 2026-10-23
