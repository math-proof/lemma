import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GroupHomomorphisms
open GroupHomomorphisms


namespace Definitions
end Definitions
namespace GroupHomomorphisms

/--
[mul_preserving_map_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupHomomorphisms.lean)
-/
@[path]
private lemma mul_preserving_map_one
  [Group G]
  [Group G']
  {f : G → G'}
-- given
  (hf : ∀ a b : G, f (a * b) = f a * f b) :
-- imply
  f 1 = 1 := by
-- proof
  apply mul_left_cancel
  calc
    _ = f (1 * 1) := (hf 1 1).symm
    _ = f 1 := by rw [mul_one]
    _ = f 1 * 1 := (mul_one _).symm

end GroupHomomorphisms

namespace GroupHomomorphisms

/--
[mul_preserving_map_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupHomomorphisms.lean)
-/
@[path]
private lemma mul_preserving_map_inv
  [Group G]
  [Group G']
  {f : G → G'}
  {a : G}
-- given
  (hf : ∀ a b : G, f (a * b) = f a * f b) :
-- imply
  f a⁻¹ = (f a)⁻¹ := by
-- proof
  have hone : f 1 = 1 := mul_preserving_map_one (f := f) hf
  apply mul_left_cancel
  calc
    _ = f (a * a⁻¹) := (hf a a⁻¹).symm
    _ = f 1 := by rw [mul_inv_cancel]
    _ = 1 := hone
    _ = f a * (f a)⁻¹ := (mul_inv_cancel _).symm

end GroupHomomorphisms

namespace GroupHomomorphisms

/--
[mul_preserving_map_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupHomomorphisms.lean)
-/
@[path]
private lemma mul_preserving_map_properties
  [Group G]
  [Group G']
  {f : G → G'}
-- given
  (hf : ∀ a b : G, f (a * b) = f a * f b) :
-- imply
  f 1 = 1 ∧ ∀ a : G, f a⁻¹ = (f a)⁻¹ :=
-- proof
  ⟨mul_preserving_map_one (f := f) hf, fun a => mul_preserving_map_inv (f := f) (a := a) hf⟩

end GroupHomomorphisms

namespace GroupHomomorphisms

/--
[card_eq_card_ker_mul_card_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupHomomorphisms.lean)
-/
@[path]
private lemma card_eq_card_ker_mul_card_range
  [Group G]
  [Group G']
  [Fintype G]
  [Fintype G']
  {f : G →* G'} [Fintype f.ker] [Fintype f.range] :
-- imply
  Fintype.card G = Fintype.card f.ker * Fintype.card f.range := by
-- proof
  classical
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  rw [h, mul_comm]
  congr 1
  exact Fintype.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

end GroupHomomorphisms


-- created on 2026-10-24
