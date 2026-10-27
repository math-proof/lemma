import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThinBox.Part5
open Finset StatMech StatMech.FrontierA


/--
[cutSpace_eq_edgePowerset_of_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma cutSpace_eq_edgePowerset_of_isTree_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
-- given
  (hG : G.IsTree) :
-- imply
  cutSpace G = G.edgeFinset.powerset := by
-- proof
  apply StatMech.FrontierA.cutSpace_eq_edgePowerset_of_isTree hG

/--
[thinBoxPlaquetteEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma thinBoxPlaquetteEdge_injective_eq
  {n : ℕ} :
-- imply
  Function.Injective (thinBoxPlaquetteEdge n) := by
-- proof
  apply StatMech.FrontierA.thinBoxPlaquetteEdge_injective n

/--
[thinBoxPlaquetteEdge_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma thinBoxPlaquetteEdge_surjective_eq
  {n : ℕ} :
-- imply
  Function.Surjective (thinBoxPlaquetteEdge n) := by
-- proof
  apply StatMech.FrontierA.thinBoxPlaquetteEdge_surjective n

/--
[thinBoxDualGraph_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma thinBoxDualGraph_isTree_eq
  {n : ℕ} :
-- imply
  (thinBoxDualGraph n).IsTree := by
-- proof
  apply StatMech.FrontierA.thinBoxDualGraph_isTree n

/--
[thinBox_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma thinBox_isClosed_eq
  {n : ℕ}
  {A : Finset (thinBoxPlaquette n)} :
-- imply
  IsClosedPlaquetteSet (thinBoxIncidence n) A := by
-- proof
  apply StatMech.FrontierA.thinBox_isClosed n A

/--
[mem_thinBoxPlaquettePreimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma mem_thinBoxPlaquettePreimage_eq
  {n : ℕ}
  {delta : Finset (Sym2 (Fin (n + 1)))}
  {p : thinBoxPlaquette n} :
-- imply
  p ∈ thinBoxPlaquettePreimage n delta ↔ (thinBoxDualEdge n p).1 ∈ delta := by
-- proof
  apply StatMech.FrontierA.mem_thinBoxPlaquettePreimage n delta p

/--
[thinBoxSurfaceEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma thinBoxSurfaceEquiv_apply_eq
  {n : ℕ}
-- given
  (A : {A : Finset (thinBoxPlaquette n) // A ∈ gaugeClosedSurfaceFamily (thinBoxIncidence n)}) :
-- imply
  (thinBoxSurfaceEquiv n A).1 = A.1.map (dualPlaquetteEmbedding (thinBoxDualEdge n)) := by
-- proof
  apply StatMech.FrontierA.thinBoxSurfaceEquiv_apply n A

/--
[thinBox_gaugePartition_isingDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean)
-/
@[path]
private lemma thinBox_gaugePartition_isingDuality_eq
  {n : ℕ}
  {K : thinBoxPlaquette n → ℝ}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  (Real.exp (∑ e ∈ (thinBoxDualGraph n).edgeFinset, dualIsingCoupling (thinBoxDualEdge n) K e) * 2) * gaugePartition (thinBoxIncidence n) K = ((2 : ℝ) ^ Fintype.card thinBoxGaugeEdge * ∏ p : thinBoxPlaquette n, Real.cosh (K p)) * ZJ (thinBoxDualGraph n).edgeFinset (dualIsingCoupling (thinBoxDualEdge n) K) (fun _ => 0) := by
-- proof
  apply StatMech.FrontierA.thinBox_gaugePartition_isingDuality n K hK


-- created on 2026-10-23
