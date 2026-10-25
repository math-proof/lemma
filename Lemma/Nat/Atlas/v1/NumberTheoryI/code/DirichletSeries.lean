import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.DirichletSeries.Part4
open ArakelovDivisor
open scoped Classical


namespace ArakelovDivisor

/--
[hasFiniteMulSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
lemma hasFiniteMulSupport
  [Field K]
  {hG : IsGlobalField K}
  {c : ArakelovDivisor K hG} :
-- imply
  (Function.mulSupport c.val).Finite :=
-- proof
  c.finite_support

end ArakelovDivisor

/--
[one_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
private lemma one_val_eq
  [Field K]
  {hG : IsGlobalField K}
  {v : hG.PlaceType} :
-- imply
  (1 : ArakelovDivisor K hG).val v = 1 := by
-- proof
  apply ArakelovDivisor.one_val v

/--
[mul_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
private lemma mul_val_eq
  [Field K]
  {hG : IsGlobalField K}
  {c d : ArakelovDivisor K hG}
  {v : hG.PlaceType} :
-- imply
  (c * d).val v = c.val v * d.val v := by
-- proof
  apply ArakelovDivisor.mul_val c d v

/--
[inv_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
private lemma inv_val_eq
  [Field K]
  {hG : IsGlobalField K}
  {c : ArakelovDivisor K hG}
  {v : hG.PlaceType} :
-- imply
  c⁻¹.val v = (c.val v)⁻¹ := by
-- proof
  apply ArakelovDivisor.inv_val c v

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
private lemma ext_eq
  [Field K]
  {hG : IsGlobalField K}
  {c d : ArakelovDivisor K hG}
-- given
  (h : ∀ v, c.val v = d.val v) :
-- imply
  c = d := by
-- proof
  apply ArakelovDivisor.ext h

/--
[size_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
private lemma size_one_eq
  [Field K]
  {hG : IsGlobalField K} :
-- imply
  (1 : ArakelovDivisor K hG).size = 1 := by
-- proof
  apply ArakelovDivisor.size_one

/--
[size_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
private lemma size_mul_eq
  [Field K]
  {hG : IsGlobalField K}
  {c d : ArakelovDivisor K hG} :
-- imply
  (c * d).size = c.size * d.size := by
-- proof
  apply ArakelovDivisor.size_mul c d

/--
[sizeHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean)
-/
@[path]
private lemma sizeHom_apply_eq
  [Field K]
  {hG : IsGlobalField K}
  {c : ArakelovDivisor K hG} :
-- imply
  sizeHom c = c.size := by
-- proof
  apply ArakelovDivisor.sizeHom_apply c


-- created on 2026-10-23
