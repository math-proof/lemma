import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ParabolicSubgroups
open Function Set CoxeterSystem
open CoxeterMatrix


/--
[zpow_eq_one_or_self_of_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicSubgroups.lean)
-/
@[path]
private lemma zpow_eq_one_or_self_of_sq_eq_one
  [Group G]
  {x : G}
  {n : ℤ}
-- given
  (h : x * x = 1) :
-- imply
  x ^ n = 1 ∨ x ^ n = x := by
-- proof
  have h_sq : x ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact h
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Int.even_or_odd n
  · left
    rw [show k + k = 2 * k from by ring, zpow_mul, h_sq, one_zpow]
  · right
    rw [show 2 * k + 1 = 2 * k + 1 from rfl]
    rw [zpow_add, zpow_mul, h_sq, one_zpow, one_mul, zpow_one]
namespace CoxeterSystem
open CoxeterMatrix
variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
local prefix:100 "s" => cs.simple
local prefix:100 "ℓ" => cs.length

namespace CoxeterSystem

/--
[simple_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicSubgroups.lean)
-/
@[path]
private lemma simple_ne_one
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i : B} :
-- imply
  s i ≠ 1 := by
-- proof
  intro h
  have h1 := cs.length_simple i
  rw [h, cs.length_one] at h1
  exact absurd h1 (by omega)

end CoxeterSystem

namespace CoxeterSystem

/--
[mul_simple_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicSubgroups.lean)
-/
@[path]
private lemma mul_simple_ne_self
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W}
  {i : B} :
-- imply
  w ≠ w * s i := by
-- proof
  intro h
  have := cs.length_mul_simple_ne w i
  rw [← h] at this
  exact this rfl

end CoxeterSystem

namespace CoxeterSystem

/--
[parabolicSubgroup_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicSubgroups.lean)
-/
@[path]
private lemma parabolicSubgroup_mono
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {T T' : Set B}
-- given
  (h : T ⊆ T') :
-- imply
  cs.parabolicSubgroup T ≤ cs.parabolicSubgroup T' :=
-- proof
  Subgroup.closure_mono (Set.image_mono h)

end CoxeterSystem


-- created on 2026-10-23
-- updated on 2026-10-24
