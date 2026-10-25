import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamConditionalHeadline
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamPairSupport_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamConditionalHeadline.lean)
-/
@[path]
private lemma grahamPairSupport_eq_pair_eq
  [Fintype V]
  [DecidableEq V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  grahamPairSupport x y = {x, y} := by
-- proof
  apply StatMech.FrontierA.grahamPairSupport_eq_pair hxy

/--
[grahamFourSupport_eq_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamConditionalHeadline.lean)
-/
@[path]
private lemma grahamFourSupport_eq_quad_eq
  [Fintype V]
  [DecidableEq V]
  {i j k l : V}
-- given
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  grahamFourSupport i j k l = {i, j, k, l} := by
-- proof
  apply StatMech.FrontierA.grahamFourSupport_eq_quad hij hik hil hjk hjl hkl

/--
[grahamCorrectedBound_of_cutPositiveAssociation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamConditionalHeadline.lean)
-/
@[path]
private lemma grahamCorrectedBound_of_cutPositiveAssociation_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 ≤ J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m)
  (hassoc : GrahamCutPositiveAssociation (grahamGraph E) 1 J m) :
-- imply
  grahamUrsell4 E J i j k l ≤ grahamCorrectedRHS E J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedBound_of_cutPositiveAssociation E J hdiag hJ hij hik hil him hjk hjl hjm hkl hkm hlm hassoc


-- created on 2026-10-23
