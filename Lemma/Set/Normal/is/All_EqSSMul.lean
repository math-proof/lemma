import Mathlib
import sympy.Basic
open MulOpposite
open scoped Pointwise


namespace NormalSubgroups

/--
[normal_iff_leftCoset_eq_rightCoset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NormalSubgroups.lean)
-/
@[path]
lemma normal_iff_leftCoset_eq_rightCoset
  [Group G]
  {H : Subgroup G} :
-- imply
  H.Normal ↔ ∀ g : G, g • (H : Set G) = op g • (H : Set G) :=
-- proof
  normal_iff_eq_cosets H

end NormalSubgroups

namespace NormalSubgroups

/--
[normal_iff_conj_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NormalSubgroups.lean)
-/
@[path]
lemma normal_iff_conj_image_eq
  [Group G]
  {H : Subgroup G} :
-- imply
  H.Normal ↔ ∀ g : G, (MulAut.conj g) '' (H : Set G) = (H : Set G) := by
-- proof
  constructor
  · intro hN g
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, MulAut.conj_apply]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hN.conj_mem h hh g
    · intro hx
      exact ⟨g⁻¹ * x * g, hN.conj_mem' x hx g, by simp [mul_assoc]⟩
  · intro h
    constructor
    intro n hn g
    have : g * n * g⁻¹ ∈ (MulAut.conj g) '' (H : Set G) :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [h g] at this

end NormalSubgroups

namespace NormalSubgroups

/--
[normal_iff_conj_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NormalSubgroups.lean)
-/
@[path]
lemma normal_iff_conj_mem
  [Group G]
  {H : Subgroup G} :
-- imply
  H.Normal ↔ ∀ n ∈ H, ∀ g : G, g * n * g⁻¹ ∈ H :=
-- proof
  ⟨fun hN => hN.conj_mem, fun h => ⟨h⟩⟩

end NormalSubgroups

namespace NormalSubgroups

/--
[normal_tfae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NormalSubgroups.lean)
-/
@[path]
lemma normal_tfae
  [Group G]
  {H : Subgroup G} :
-- imply
  List.TFAE [ H.Normal, ∀ g : G, g • (H : Set G) = op g • (H : Set G), ∀ g : G, (MulAut.conj g) '' (H : Set G) = (H : Set G), ∀ n ∈ H, ∀ g : G, g * n * g⁻¹ ∈ H ] := by
-- proof
  tfae_have 1 ↔ 2 := normal_iff_leftCoset_eq_rightCoset H
  tfae_have 1 ↔ 3 := normal_iff_conj_image_eq H
  tfae_have 1 ↔ 4 := normal_iff_conj_mem H
  tfae_finish

end NormalSubgroups


-- created on 2026-10-23
