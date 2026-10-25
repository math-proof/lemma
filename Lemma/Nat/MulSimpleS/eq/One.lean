import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.BruhatOrder
open CoxeterBruhat


namespace Definitions
end Definitions
namespace CoxeterBruhat

/--
[simple_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma simple_sq
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i : B} :
-- imply
  cs.simple i * cs.simple i = 1 := by
-- proof
  have h := cs.simple_mul_simple_cancel_left (w := 1) i; rwa [mul_one] at h

end CoxeterBruhat

namespace CoxeterBruhat

/--
[simple_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma simple_inv
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i : B} :
-- imply
  (cs.simple i)⁻¹ = cs.simple i :=
-- proof
  inv_eq_of_mul_eq_one_right (simple_sq cs i)

end CoxeterBruhat

namespace CoxeterBruhat

/--
[reflection_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma reflection_sq
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {t : W}
-- given
  (ht : t ∈ reflections M cs) :
-- imply
  t * t = 1 := by
-- proof
  obtain ⟨w, i, rfl⟩ := ht
  have h1 : (w * cs.simple i * w⁻¹) * (w * cs.simple i * w⁻¹)
    = w * (cs.simple i * cs.simple i) * w⁻¹ := by group
  rw [h1, simple_sq cs i]; group

end CoxeterBruhat

namespace CoxeterBruhat

/--
[reflection_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma reflection_inv
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {t : W}
-- given
  (ht : t ∈ reflections M cs) :
-- imply
  t⁻¹ = t :=
-- proof
  inv_eq_of_mul_eq_one_right (reflection_sq cs ht)

end CoxeterBruhat

namespace CoxeterBruhat

/--
[simple_mem_reflections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma simple_mem_reflections
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i : B} :
-- imply
  cs.simple i ∈ reflections M cs :=
-- proof
  ⟨1, i, by simp⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[simple_conj_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma simple_conj_reflection
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {t : W}
  {i : B}
-- given
  (ht : t ∈ reflections M cs) :
-- imply
  cs.simple i * t * cs.simple i ∈ reflections M cs := by
-- proof
  obtain ⟨w, j, rfl⟩ := ht
  refine ⟨cs.simple i * w, j, ?_⟩
  rw [mul_inv_rev, simple_inv cs i]; group

end CoxeterBruhat

namespace CoxeterBruhat

/--
[mul_simple_conj_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma mul_simple_conj_eq
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {t : W}
  {i : B}
-- given
  (hvw : v * t = w) :
-- imply
  (v * cs.simple i) * (cs.simple i * t * cs.simple i) = w * cs.simple i := by
-- proof
  have : v * cs.simple i * (cs.simple i * t * cs.simple i)
    = v * (cs.simple i * cs.simple i) * t * cs.simple i := by group
  rw [this, simple_sq cs i, mul_one, ← hvw]

end CoxeterBruhat

namespace CoxeterBruhat

/--
[mul_reflection_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma mul_reflection_reverse
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {a b : W}
  {t : W}
-- given
  (ht : t ∈ reflections M cs)
  (h : a * t = b) :
-- imply
  b * t = a := by
-- proof
  rw [← h, mul_assoc, reflection_sq cs ht, mul_one]

end CoxeterBruhat

namespace CoxeterBruhat

/--
[reflection_length_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma reflection_length_odd
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {t : W}
-- given
  (ht : t ∈ reflections M cs) :
-- imply
  cs.length t % 2 = 1 := by
-- proof
  obtain ⟨u, j, rfl⟩ := ht
  have h : cs.lengthParity (u * cs.simple j * u⁻¹) = Multiplicative.ofAdd 1 := by
    simp [map_mul, cs.lengthParity_simple, map_inv]
  rw [cs.lengthParity_eq_ofAdd_length] at h
  have h1 : (cs.length (u * cs.simple j * u⁻¹) : ZMod 2) = ((1 : ℕ) : ZMod 2) := by
    have := Multiplicative.ofAdd.injective h; simpa using this
  rwa [ZMod.natCast_eq_natCast_iff'] at h1

end CoxeterBruhat

namespace CoxeterBruhat

/--
[length_parity_ne_of_mul_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma length_parity_ne_of_mul_reflection
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w t : W}
-- given
  (ht : t ∈ reflections M cs)
  (hvw : v * t = w) :
-- imply
  cs.length v % 2 ≠ cs.length w % 2 := by
-- proof
  have h1 := cs.length_mul_mod_two v t; rw [hvw] at h1
  have h2 := reflection_length_odd cs ht; omega

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatStep_length_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatStep_length_lt
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
-- given
  (h : BruhatStep cs v w) :
-- imply
  cs.length v < cs.length w := by
-- proof
  obtain ⟨_, _, _, hlen⟩ := h; exact hlen

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatLE_length_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatLE_length_le
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
-- given
  (h : BruhatLE cs v w) :
-- imply
  cs.length v ≤ cs.length w := by
-- proof
  induction h with
  | refl => exact Nat.le_refl _
  | @tail _ c _ hbc ih => exact le_of_lt (lt_of_le_of_lt ih (bruhatStep_length_lt cs hbc))

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatLE_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatLE_refl
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W} :
-- imply
  BruhatLE cs w w :=
-- proof
  Relation.ReflTransGen.refl

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatLE_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatLE_trans
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {u v w : W}
-- given
  (h0 : BruhatLE cs u v)
  (h1 : BruhatLE cs v w) :
-- imply
  BruhatLE cs u w :=
-- proof
  h1.trans h2

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatLE_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatLE_of_step
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
-- given
  (h : BruhatStep cs v w) :
-- imply
  BruhatLE cs v w :=
-- proof
  Relation.ReflTransGen.single h

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatStep_mul_simple_descent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatStep_mul_simple_descent
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v : W}
  {i : B}
-- given
  (h : cs.length (v * cs.simple i) < cs.length v) :
-- imply
  BruhatStep cs (v * cs.simple i) v :=
-- proof
  ⟨cs.simple i, simple_mem_reflections cs i,
    by rw [mul_assoc, simple_sq cs i, mul_one], h⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatLE_eq_of_length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatLE_eq_of_length_eq
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
-- given
  (h : BruhatLE cs v w)
  (hlen : cs.length v = cs.length w) :
-- imply
  v = w := by
-- proof
  induction h with
  | refl => rfl
  | @tail _ c _ hbc ih =>
    have hlen_bc := bruhatStep_length_lt cs hbc
    have hlen_vb := bruhatLE_length_le cs (by assumption)
    omega

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhat_lifting_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhat_lifting_lemma
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {t : W}
  {i : B}
-- given
  (hSEC : StrongExchangeForBruhat cs)
  (ht : t ∈ reflections M cs)
  (hvt : v * t = w)
  (hcover : cs.length v + 1 = cs.length w)
  (hv_up : ¬cs.IsRightDescent v i)
  (hne : v * cs.simple i ≠ w) :
-- imply
  ¬cs.IsRightDescent w i ∧ BruhatStep cs (v * cs.simple i) (w * cs.simple i) := by
-- proof
  have hw_up : ¬cs.IsRightDescent w i := by
    intro hw_desc
    exact hne (hSEC v w t ht hvt hcover i hv_up hw_desc)
  constructor
  · exact hw_up
  ·
    rw [CoxeterSystem.not_isRightDescent_iff] at hv_up hw_up
    exact ⟨cs.simple i * t * cs.simple i,
      simple_conj_reflection cs ht i,
      mul_simple_conj_eq cs hvt i,
      by rw [hv_up, hw_up]; omega⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatStep_right_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhatStep_right_mul
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {i : B}
-- given
  (hSEC : StrongExchangeForBruhat cs)
  (hvw : BruhatStep cs v w) :
-- imply
  BruhatLE cs (v * cs.simple i) w ∨ BruhatLE cs (v * cs.simple i) (w * cs.simple i) := by
-- proof
  obtain ⟨t, ht, hvt, hlen⟩ := hvw
  by_cases hv : cs.IsRightDescent v i
  ·
    left
    exact (bruhatLE_of_step cs (bruhatStep_mul_simple_descent cs i hv)).trans
      (bruhatLE_of_step cs ⟨t, ht, hvt, hlen⟩)
  ·
    rw [CoxeterSystem.not_isRightDescent_iff] at hv
    by_cases hw : cs.IsRightDescent w i
    ·
      rw [cs.isRightDescent_iff] at hw
      have ht' : cs.simple i * t * cs.simple i ∈ reflections M cs :=
        simple_conj_reflection cs ht i
      have hvs_ws : (v * cs.simple i) * (cs.simple i * t * cs.simple i) =
        w * cs.simple i := mul_simple_conj_eq cs hvt i
      by_cases heq : v * cs.simple i = w
      ·
        left; rw [heq]; exact bruhatLE_refl cs w
      ·
        by_cases hgap : cs.length v + 1 = cs.length w
        ·
          exfalso
          exact heq (hSEC v w t ht hvt hgap i
            (by rwa [CoxeterSystem.not_isRightDescent_iff])
            (by rwa [cs.isRightDescent_iff]))
        ·
          have hparity := length_parity_ne_of_mul_reflection cs ht hvt
          have hgap' : cs.length w ≥ cs.length v + 3 := by omega
          have h_lt : cs.length (v * cs.simple i) < cs.length (w * cs.simple i) := by
            rw [hv]; omega
          right
          exact bruhatLE_of_step cs ⟨cs.simple i * t * cs.simple i, ht', hvs_ws, h_lt⟩
    ·
      rw [CoxeterSystem.not_isRightDescent_iff] at hw
      right
      have h_lt : cs.length (v * cs.simple i) < cs.length (w * cs.simple i) := by
        rw [hv, hw]; exact Nat.add_lt_add_right hlen 1
      exact bruhatLE_of_step cs
        ⟨cs.simple i * t * cs.simple i, simple_conj_reflection cs ht i,
          mul_simple_conj_eq cs hvt i, h_lt⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhat_right_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatOrder.lean)
-/
@[path]
private lemma bruhat_right_mul
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {i : B}
-- given
  (hSEC : StrongExchangeForBruhat cs)
  (hvw : BruhatLE cs v w) :
-- imply
  BruhatLE cs (v * cs.simple i) w ∨ BruhatLE cs (v * cs.simple i) (w * cs.simple i) := by
-- proof
  induction hvw with
  | refl => right; exact bruhatLE_refl cs _
  | @tail b c _ hbc ih =>
    obtain ih_left | ih_right := ih
    ·
      left; exact ih_left.trans (bruhatLE_of_step cs hbc)
    ·
      obtain hbc_left | hbc_right := bruhatStep_right_mul cs hSEC hbc i
      · left; exact ih_right.trans hbc_left
      · right; exact ih_right.trans hbc_right

end CoxeterBruhat


-- created on 2026-10-24
