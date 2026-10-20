import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ModularForms.JacobiTheta.Ramanujan
open MetaMathlibExt


/--
[ramanujanThetaTerm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanThetaTerm_zero_eq
  {a b : ℂ} :
-- imply
  ramanujanThetaTerm a b 0 = 1 := by
-- proof
  apply MetaMathlibExt.ramanujanThetaTerm_zero a b

/--
[ramanujanThetaTerm_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanThetaTerm_one_eq
  {a b : ℂ} :
-- imply
  ramanujanThetaTerm a b 1 = a := by
-- proof
  apply MetaMathlibExt.ramanujanThetaTerm_one a b

/--
[ramanujanThetaTerm_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanThetaTerm_neg_one_eq
  {a b : ℂ} :
-- imply
  ramanujanThetaTerm a b (-1) = b := by
-- proof
  apply MetaMathlibExt.ramanujanThetaTerm_neg_one a b

/--
[ramanujanThetaTerm_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanThetaTerm_neg_eq
  {a b : ℂ}
  {n : ℤ} :
-- imply
  ramanujanThetaTerm a b (-n) = ramanujanThetaTerm b a n := by
-- proof
  apply MetaMathlibExt.ramanujanThetaTerm_neg a b n

/--
[ramanujanTheta_summable_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanTheta_summable_symm_eq
  {a b : ℂ} :
-- imply
  Summable (ramanujanThetaTerm a b) ↔ Summable (ramanujanThetaTerm b a) := by
-- proof
  apply MetaMathlibExt.ramanujanTheta_summable_symm a b

/--
[ramanujanThetaRaw_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanThetaRaw_symm_eq
  {a b : ℂ} :
-- imply
  ramanujanThetaRaw a b = ramanujanThetaRaw b a := by
-- proof
  apply MetaMathlibExt.ramanujanThetaRaw_symm a b

/--
[ramanujanTheta_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanTheta_symm_eq
  {a b : ℂ}
-- given
  (h : Summable (ramanujanThetaTerm a b)) :
-- imply
  ramanujanTheta a b h =
    ramanujanTheta b a ((ramanujanTheta_summable_symm a b).mp h) := by
-- proof
  apply MetaMathlibExt.ramanujanTheta_symm a b h

/--
[not_summable_ramanujanThetaTerm_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma not_summable_ramanujanThetaTerm_one_one_eq
  :
-- imply
  ¬Summable (ramanujanThetaTerm 1 1) := by
-- proof
  apply MetaMathlibExt.not_summable_ramanujanThetaTerm_one_one

/--
[ramanujanThetaRaw_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean)
-/
@[path]
private lemma ramanujanThetaRaw_one_one_eq
  :
-- imply
  ramanujanThetaRaw 1 1 = 0 := by
-- proof
  apply MetaMathlibExt.ramanujanThetaRaw_one_one


-- created on 2026-10-20
