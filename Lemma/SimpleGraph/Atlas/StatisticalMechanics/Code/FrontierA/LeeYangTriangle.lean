import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part4
open Finset Polynomial StatMech StatMech.FrontierA


/--
[threeVertexTriangle_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma threeVertexTriangle_edgeFinset_eq :
-- imply
  threeVertexTriangle.edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
-- proof
  apply StatMech.FrontierA.threeVertexTriangle_edgeFinset

/--
[sum_bond_threeVertexTriangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma sum_bond_threeVertexTriangle_eq
  {s : ConfigSpace (Fin 3)} :
-- imply
  (∑ e ∈ threeVertexTriangle.edgeFinset, bond s e) = bond s s(0, 1) + bond s s(0, 2) + bond s s(1, 2) := by
-- proof
  apply StatMech.FrontierA.sum_bond_threeVertexTriangle s

/--
[minusSpinCount_finThree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma minusSpinCount_finThree_eq
  {s : ConfigSpace (Fin 3)} :
-- imply
  minusSpinCount s = (if s 0 = false then 1 else 0) + (if s 1 = false then 1 else 0) + (if s 2 = false then 1 else 0) := by
-- proof
  apply StatMech.FrontierA.minusSpinCount_finThree s

/--
[leeYangPolynomial_threeVertexTriangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma leeYangPolynomial_threeVertexTriangle_eq
  {beta : ℝ} :
-- imply
  leeYangPolynomial threeVertexTriangle beta = C (Real.exp (3 * beta)) * (1 + X ^ 3) + C (3 * Real.exp (-beta)) * (X + X ^ 2) := by
-- proof
  apply StatMech.FrontierA.leeYangPolynomial_threeVertexTriangle beta

/--
[leeYangPolynomial_threeVertexTriangle_factored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma leeYangPolynomial_threeVertexTriangle_factored_eq
  {beta : ℝ} :
-- imply
  leeYangPolynomial threeVertexTriangle beta = C (Real.exp (3 * beta)) * (X + 1) * (X ^ 2 + C (3 * Real.exp (-4 * beta) - 1) * X + 1) := by
-- proof
  apply StatMech.FrontierA.leeYangPolynomial_threeVertexTriangle_factored beta

/--
[leeYangComplexPolynomial_threeVertexTriangle_factored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_threeVertexTriangle_factored_eq
  {beta : ℝ} :
-- imply
  leeYangComplexPolynomial threeVertexTriangle beta = C (Real.exp (3 * beta) : ℂ) * (X + 1) * (X ^ 2 + C (3 * Real.exp (-4 * beta) - 1 : ℂ) * X + 1) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_threeVertexTriangle_factored beta

/--
[palindromicQuadratic_root_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma palindromicQuadratic_root_norm_eq
  {c : ℝ}
  {z : ℂ}
-- given
  (hcLower : -2 ≤ c)
  (hcUpper : c ≤ 2)
  (hz : z ^ 2 + (c : ℂ) * z + 1 = 0) :
-- imply
  ‖z‖ = 1 := by
-- proof
  apply StatMech.FrontierA.palindromicQuadratic_root_norm hcLower hcUpper hz

/--
[leeYang_threeVertexTriangle_root_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma leeYang_threeVertexTriangle_root_norm_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 ≤ beta)
  (hz : (leeYangComplexPolynomial threeVertexTriangle beta).eval z = 0) :
-- imply
  ‖z‖ = 1 := by
-- proof
  apply StatMech.FrontierA.leeYang_threeVertexTriangle_root_norm hbeta hz

/--
[hasLeeYangCircle_threeVertexTriangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma hasLeeYangCircle_threeVertexTriangle_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  HasLeeYangCircle threeVertexTriangle beta := by
-- proof
  apply StatMech.FrontierA.hasLeeYangCircle_threeVertexTriangle hbeta

/--
[finiteTriangleGraph_hasLeeYangCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma finiteTriangleGraph_hasLeeYangCircle_eq
  {t : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  HasLeeYangCircle (finiteTriangleGraph t) beta := by
-- proof
  apply StatMech.FrontierA.finiteTriangleGraph_hasLeeYangCircle t hbeta

/--
[finiteSmallComponentGraph_hasLeeYangCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean)
-/
@[path]
private lemma finiteSmallComponentGraph_hasLeeYangCircle_eq
  {i e t : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  HasLeeYangCircle (finiteSmallComponentGraph i e t) beta := by
-- proof
  apply StatMech.FrontierA.finiteSmallComponentGraph_hasLeeYangCircle i e t hbeta


-- created on 2026-10-23
