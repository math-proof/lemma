import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField.Part2
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[vertexGhostCoupling_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexGhostCoupling_some_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {x y : V} :
-- imply
  vertexGhostCoupling J H s(some x, some y) = J s(x, y) := by
-- proof
  apply StatMech.Sharpness.vertexGhostCoupling_some_some G J H x y

/--
[vertexGhostCoupling_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexGhostCoupling_some_none_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {x : V} :
-- imply
  vertexGhostCoupling J H s(some x, none) = H x := by
-- proof
  apply StatMech.Sharpness.vertexGhostCoupling_some_none G J H x

/--
[vertexGhost_bondSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexGhost_bondSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {s : ConfigSpace (Option V)} :
-- imply
  (∑ e ∈ (withGhost G).edgeFinset, vertexGhostCoupling J H e * bond s e) = (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e)) + spin s none * ∑ x : V, H x * spin s (some x) := by
-- proof
  apply StatMech.Sharpness.vertexGhost_bondSum G J H s

/--
[vertexGhost_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexGhost_weight_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {s : ConfigSpace (Option V)} :
-- imply
  boltzmannJ (withGhost G) beta (vertexGhostCoupling J H) s = vertexFieldWeight G beta J (fun x ↦ spin s none * H x) (fun x ↦ s (some x)) := by
-- proof
  apply StatMech.Sharpness.vertexGhost_weight_eq G beta J H s

/--
[vertexFieldWeight_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexFieldWeight_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {s : ConfigSpace V} :
-- imply
  vertexFieldWeight G beta J (fun x ↦ -H x) (flipV s) = vertexFieldWeight G beta J H s := by
-- proof
  apply StatMech.Sharpness.vertexFieldWeight_flip G beta J H s

/--
[vertexFieldZ_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexFieldZ_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ} :
-- imply
  vertexFieldZ G beta J (fun x ↦ -H x) = vertexFieldZ G beta J H := by
-- proof
  apply StatMech.Sharpness.vertexFieldZ_neg G beta J H

/--
[vertexFieldNum_neg_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexFieldNum_neg_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {A : Finset V}
-- given
  (hA : Even A.card) :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * vertexFieldWeight G beta J (fun x ↦ -H x) s) = ∑ s : ConfigSpace V, spinProd A s * vertexFieldWeight G beta J H s := by
-- proof
  apply StatMech.Sharpness.vertexFieldNum_neg_even G beta J H A hA

/--
[vertexGhost_partition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexGhost_partition_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ} :
-- imply
  partitionJ (withGhost G) beta (vertexGhostCoupling J H) = 2 * vertexFieldZ G beta J H := by
-- proof
  apply StatMech.Sharpness.vertexGhost_partition_eq G beta J H

/--
[vertexGhost_expectation_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexGhost_expectation_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {A : Finset V}
-- given
  (hA : Even A.card) :
-- imply
  expectationJ (withGhost G) beta (vertexGhostCoupling J H) (A.map someEmb) = vertexFieldExpectation G beta J H (spinProd A) := by
-- proof
  apply StatMech.Sharpness.vertexGhost_expectation_eq G beta J H A hA

/--
[vertexGhost_twoPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexGhost_twoPoint_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {a b : V} :
-- imply
  twoPointJ (withGhost G) beta (vertexGhostCoupling J H) (some a) (some b) = vertexFieldTwoPoint G beta J H a b := by
-- proof
  apply StatMech.Sharpness.vertexGhost_twoPoint_eq G beta J H a b

/--
[vertexFieldTwoPoint_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexFieldTwoPoint_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {a b : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hH : ∀ x, 0 ≤ H x) :
-- imply
  0 ≤ vertexFieldTwoPoint G beta J H a b := by
-- proof
  apply StatMech.Sharpness.vertexFieldTwoPoint_nonneg G beta J H hbeta hJ hH a b

/--
[couplingIn_vertexGhost_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma couplingIn_vertexGhost_map_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {S : Finset V} :
-- imply
  couplingIn (vertexGhostCoupling J H) (S.map someEmb) = vertexGhostCoupling (couplingIn J S) (fun _ ↦ 0) := by
-- proof
  apply StatMech.Sharpness.couplingIn_vertexGhost_map_some G J H S

/--
[vertexFieldTwoPoint_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexFieldTwoPoint_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {a b : V} :
-- imply
  vertexFieldTwoPoint G beta J (fun _ ↦ 0) a b = twoPointJ G beta J a b := by
-- proof
  apply StatMech.Sharpness.vertexFieldTwoPoint_zero G beta J a b

/--
[twoPointJ_couplingIn_vertexGhost_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma twoPointJ_couplingIn_vertexGhost_map_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {S : Finset V}
  {a b : V} :
-- imply
  twoPointJ (withGhost G) beta (couplingIn (vertexGhostCoupling J H) (S.map someEmb)) (some a) (some b) = twoPointJ G beta (couplingIn J S) a b := by
-- proof
  apply StatMech.Sharpness.twoPointJ_couplingIn_vertexGhost_map_some G beta J H S a b

/--
[vertexFieldTwoPoint_simon_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempVertexField.lean)
-/
@[path]
private lemma vertexFieldTwoPoint_simon_finite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : V → ℝ}
  {S : Finset V}
  {o z : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hH : ∀ x, 0 ≤ H x)
  (hHS : ∀ x ∈ S, H x = 0)
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  vertexFieldTwoPoint G beta J H o z ≤ ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S), Real.tanh (beta * J s(x, y)) * twoPointJ G beta (couplingIn J S) o x * vertexFieldTwoPoint G beta J H y z := by
-- proof
  apply StatMech.Sharpness.vertexFieldTwoPoint_simon_finite G beta J H hbeta hJ hH S hHS o z ho hz


-- created on 2026-10-23
