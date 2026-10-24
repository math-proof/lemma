import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.BoundaryRusso
open Finset StatMech StatMech.FK


/--
[hasDerivAt_bcWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma hasDerivAt_bcWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p : ℝ}
  {q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun p => bcWeight G C p q ω) (bcWeight G C p q ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_bcWeight G C hp hp1 q ω

/--
[hasDerivAt_bcNumer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma hasDerivAt_bcNumer_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  HasDerivAt (fun p => bcNumer G C p q g) ((∑ ω, g ω * (bcWeight G C p q ω * ∑ e ∈ G.edgeFinset, (coord e ω - p))) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_bcNumer G C hp hp1 q g

/--
[bcNumer_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcNumer_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ} :
-- imply
  bcNumer G C p q (fun _ => 1) = bcZ G C p q := by
-- proof
  apply StatMech.FK.bcNumer_one G C p q

/--
[bcMean_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcMean_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  bcMean G C p q g = bcNumer G C p q g / bcZ G C p q := by
-- proof
  apply StatMech.FK.bcMean_eq_div G C p q g

/--
[bcMean_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcMean_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
-- given
  (g h : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  bcMean G C p q (fun ω => g ω + h ω) = bcMean G C p q g + bcMean G C p q h := by
-- proof
  apply StatMech.FK.bcMean_add G C p q g h

/--
[bcMean_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcMean_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {s : Finset ι}
  {g : ι → ConfigSpace (Sym2 V) → ℝ} :
-- imply
  bcMean G C p q (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, bcMean G C p q (g i) := by
-- proof
  apply StatMech.FK.bcMean_sum G C p q s g

/--
[bcMean_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcMean_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {c : ℝ}
-- given
  (hZ : bcZ G C p q ≠ 0) :
-- imply
  bcMean G C p q (fun _ => c) = c := by
-- proof
  apply StatMech.FK.bcMean_const G C p q hZ

/--
[bcMean_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcMean_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q c : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  bcMean G C p q (fun ω => c * g ω) = c * bcMean G C p q g := by
-- proof
  apply StatMech.FK.bcMean_const_mul G C p q c g

/--
[bcCov_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcCov_sum_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {s : Finset ι}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {g : ι → ConfigSpace (Sym2 V) → ℝ} :
-- imply
  bcCov G C p q f (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, bcCov G C p q f (g i) := by
-- proof
  apply StatMech.FK.bcCov_sum_right G C p q s f g

/--
[bcCov_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcCov_sub_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ}
  {c : ℝ}
-- given
  (hZ : bcZ G C p q ≠ 0) :
-- imply
  bcCov G C p q f (fun ω => g ω - c) = bcCov G C p q f g := by
-- proof
  apply StatMech.FK.bcCov_sub_const G C p q f g hZ

/--
[bcCov_centeredCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma bcCov_centeredCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hZ : bcZ G C p q ≠ 0) :
-- imply
  bcCov G C p q g (fun ω => ∑ e ∈ G.edgeFinset, (coord e ω - p)) = ∑ e ∈ G.edgeFinset, bcCov G C p q g (coord e) := by
-- proof
  apply StatMech.FK.bcCov_centeredCount G C p q hZ g

/--
[hasDerivAt_bcMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma hasDerivAt_bcMean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun p => bcMean G C p q g) ((∑ e ∈ G.edgeFinset, bcCov G C p q g (coord e)) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_bcMean G C hp hp1 hq g

/--
[hasDerivAt_bcProbOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean)
-/
@[path]
private lemma hasDerivAt_bcProbOf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun p => bcProbOf G C p q A) ((∑ e ∈ G.edgeFinset, bcCov G C p q (A.indicator fun _ => (1 : ℝ)) (coord e)) / (p * (1 - p))) p := by
-- proof
  apply StatMech.FK.hasDerivAt_bcProbOf G C hp hp1 hq A


-- created on 2026-10-23
