import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge
open Finset Polynomial StatMech StatMech.FrontierA


/--
[twoVertexEdge_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma twoVertexEdge_edgeFinset_eq :
-- imply
  twoVertexEdge.edgeFinset = {s(0, 1)} := by
-- proof
  apply StatMech.FrontierA.twoVertexEdge_edgeFinset

/--
[minusSpinCount_finTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma minusSpinCount_finTwo_eq
  {s : ConfigSpace (Fin 2)} :
-- imply
  minusSpinCount s = (if s 0 = false then 1 else 0) + (if s 1 = false then 1 else 0) := by
-- proof
  apply StatMech.FrontierA.minusSpinCount_finTwo s

/--
[leeYangPolynomial_twoVertexEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma leeYangPolynomial_twoVertexEdge_eq
  {beta : ℝ} :
-- imply
  leeYangPolynomial twoVertexEdge beta = C (Real.exp beta) * (1 + X ^ 2) + C (2 * Real.exp (-beta)) * X := by
-- proof
  apply StatMech.FrontierA.leeYangPolynomial_twoVertexEdge beta

/--
[leeYangPolynomial_twoVertexEdge_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma leeYangPolynomial_twoVertexEdge_normalized_eq
  {beta : ℝ} :
-- imply
  leeYangPolynomial twoVertexEdge beta = C (Real.exp beta) * (X ^ 2 + C (2 * Real.exp (-2 * beta)) * X + 1) := by
-- proof
  apply StatMech.FrontierA.leeYangPolynomial_twoVertexEdge_normalized beta

/--
[leeYangComplexPolynomial_twoVertexEdge_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_twoVertexEdge_normalized_eq
  {beta : ℝ} :
-- imply
  leeYangComplexPolynomial twoVertexEdge beta = C (Real.exp beta : ℂ) * (X ^ 2 + C (2 * Real.exp (-2 * beta) : ℂ) * X + 1) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_twoVertexEdge_normalized beta

/--
[leeYang_twoVertexEdge_root_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma leeYang_twoVertexEdge_root_equation_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hz : (leeYangComplexPolynomial twoVertexEdge beta).eval z = 0) :
-- imply
  z ^ 2 + (2 * Real.exp (-2 * beta) : ℂ) * z + 1 = 0 := by
-- proof
  apply StatMech.FrontierA.leeYang_twoVertexEdge_root_equation beta hz

/--
[leeYang_twoVertexEdge_root_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma leeYang_twoVertexEdge_root_norm_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hz : (leeYangComplexPolynomial twoVertexEdge beta).eval z = 0) :
-- imply
  ‖z‖ = 1 := by
-- proof
  apply StatMech.FrontierA.leeYang_twoVertexEdge_root_norm hbeta hz

/--
[HasLeeYangCircle.sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma sum_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {beta : ℝ}
-- given
  (hG : HasLeeYangCircle G beta)
  (hH : HasLeeYangCircle H beta) :
-- imply
  HasLeeYangCircle (G ⊕g H) beta := by
-- proof
  apply StatMech.FrontierA.HasLeeYangCircle.sum G H hG hH

/--
[hasLeeYangCircle_twoVertexEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma hasLeeYangCircle_twoVertexEdge_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  HasLeeYangCircle twoVertexEdge beta := by
-- proof
  apply StatMech.FrontierA.hasLeeYangCircle_twoVertexEdge hbeta

/--
[leeYangComplexPolynomial_finiteMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_finiteMatching_eq
  {n : ℕ}
  {beta : ℝ} :
-- imply
  leeYangComplexPolynomial (finiteMatching n) beta = (leeYangComplexPolynomial twoVertexEdge beta) ^ n := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_finiteMatching n beta

/--
[finiteMatching_hasLeeYangCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean)
-/
@[path]
private lemma finiteMatching_hasLeeYangCircle_eq
  {n : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  HasLeeYangCircle (finiteMatching n) beta := by
-- proof
  apply StatMech.FrontierA.finiteMatching_hasLeeYangCircle n hbeta


-- created on 2026-10-23
