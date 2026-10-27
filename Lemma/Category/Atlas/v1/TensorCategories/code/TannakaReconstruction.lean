import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
open CategoryTheory


variable (k : Type u) [CommRing k] (A : Type u) [Ring A] [Algebra k A]
/--
[endForget₂_algebraMap_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean)
-/
@[path]
through the central algebra map `k → A`. -/
lemma endForget₂_algebraMap_comm (r : k) (x : EndForget₂ A) :
  endForget₂AlgebraMap k A r * x = x * endForget₂AlgebraMap k A r := by
  unfold endForget₂AlgebraMap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  set a := (ringEquivEndForget₂ A).symm x
  have hx : x = ringEquivEndForget₂ A a := (ringEquivEndForget₂ A).apply_symm_apply x ▸ rfl
  rw [hx, ← map_mul, ← map_mul, Algebra.commutes]

/--
[endForget](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean)
-/
@[path]
private lemma endForget_eq
  {k : Type u}
  [CommRing k]
  {A : Type u}
  [Ring A]
  [Algebra k A]
  {r : k}
  {x : EndForget₂ A} :
-- imply
  endForget₂AlgebraMap k A r * x = x * endForget₂AlgebraMap k A r := by
-- proof
  apply endForget k A r x


-- created on 2026-10-23
