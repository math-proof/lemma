import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.HeckeAlgebra.GenericAlgebraUniqueness
open HeckeAlgebra
open scoped Classical


namespace HeckeAlgebra

/--
[basis_eq_of_h_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/GenericAlgebraUniqueness.lean)
-/
@[path]
private lemma basis_eq_of_h_basis
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {H₁ H₂ : HeckeMultiplication M' R' C}
  {w : M'.Group}
-- given
  (h_basis : H₁.basis = H₂.basis) :
-- imply
  H₁.basis w = H₂.basis w :=
-- proof
  congr_fun h_basis w

end HeckeAlgebra

namespace HeckeAlgebra

/--
[HeckeMultiplication.mul_gen_basis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/GenericAlgebraUniqueness.lean)
-/
@[path]
private lemma HeckeMultiplication.mul_gen_basis_eq
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {H₁ H₂ : HeckeMultiplication M' R' C}
  {s : B'}
  {w : M'.Group}
-- given
  (h_basis : H₁.basis = H₂.basis)
  (h_add : H₁.add = H₂.add)
  (h_smul : H₁.smul = H₂.smul)
  (h_sc : H₁.sc = H₂.sc) :
-- imply
  H₁.mul (H₁.basis (M'.toCoxeterSystem.simple s)) (H₁.basis w) = H₂.mul (H₁.basis (M'.toCoxeterSystem.simple s)) (H₁.basis w) := by
-- proof
  have hbs := basis_eq_of_h_basis h_basis
  obtain h_up | h_down := M'.toCoxeterSystem.length_simple_mul w s
  ·
    have hgt : M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) >
      M'.toCoxeterSystem.length w := by omega
    rw [H₁.length_up s w hgt]
    rw [show H₁.basis (M'.toCoxeterSystem.simple s) = H₂.basis (M'.toCoxeterSystem.simple s)
      from hbs _, show H₁.basis w = H₂.basis w from hbs w]
    rw [H₂.length_up s w hgt, ← hbs]
  ·
    have hlt : M'.toCoxeterSystem.length (M'.toCoxeterSystem.simple s * w) <
      M'.toCoxeterSystem.length w := by omega
    rw [H₁.length_down s w hlt]
    rw [show H₁.basis (M'.toCoxeterSystem.simple s) = H₂.basis (M'.toCoxeterSystem.simple s)
      from hbs _, show H₁.basis w = H₂.basis w from hbs w]
    rw [H₂.length_down s w hlt]
    simp only [hbs, h_add, h_smul, h_sc]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[HeckeMultiplication.mul_gen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/GenericAlgebraUniqueness.lean)
-/
@[path]
private lemma HeckeMultiplication.mul_gen_eq
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {H₁ H₂ : HeckeMultiplication M' R' C}
  {s : B'}
  {z : C}
-- given
  (h_basis : H₁.basis = H₂.basis)
  (h_add : H₁.add = H₂.add)
  (h_smul : H₁.smul = H₂.smul)
  (h_sc : H₁.sc = H₂.sc) :
-- imply
  H₁.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z = H₂.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z := by
-- proof
  apply H₁.basis_span (fun z =>
    H₁.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z =
    H₂.mul (H₁.basis (M'.toCoxeterSystem.simple s)) z)
  · intro w
    exact H₁.mul_gen_basis_eq H₂ h_basis h_add h_smul h_sc s w
  ·
    intro x y hx hy
    rw [H₁.mul_add_right, hx, hy]
    simp only [show H₁.add = H₂.add from h_add]
    rw [← H₂.mul_add_right]
  ·
    intro r x hx
    rw [H₁.mul_smul_right, hx]
    simp only [show H₁.smul = H₂.smul from h_smul]
    rw [← H₂.mul_smul_right]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[HeckeMultiplication.mul_basis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/GenericAlgebraUniqueness.lean)
-/
@[path]
private lemma HeckeMultiplication.mul_basis_eq
  {M' : CoxeterMatrix B'}
  [CommRing R']
  {H₁ H₂ : HeckeMultiplication M' R' C}
-- given
  (h_basis : H₁.basis = H₂.basis)
  (h_add : H₁.add = H₂.add)
  (h_smul : H₁.smul = H₂.smul)
  (h_sc : H₁.sc = H₂.sc) :
-- imply
  ∀ (w : M'.Group) (z : C), H₁.mul (H₁.basis w) z = H₂.mul (H₁.basis w) z := by
-- proof
  have hbs := basis_eq_of_h_basis h_basis
  suffices ∀ (n : ℕ) (w : M'.Group),
    M'.toCoxeterSystem.length w ≤ n →
    ∀ z, H₁.mul (H₁.basis w) z = H₂.mul (H₁.basis w) z by
    intro w z
    exact this (M'.toCoxeterSystem.length w) w le_rfl z
  intro n
  induction n with
  | zero =>
    intro w hw z
    have hw1 : w = 1 :=
      M'.toCoxeterSystem.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    rw [H₁.identity_left, hbs, H₂.identity_left]
  | succ n ih =>
    intro w hw z
    by_cases hw1 : w = 1
    · subst hw1
      rw [H₁.identity_left, hbs, H₂.identity_left]
    · obtain ⟨s, hs⟩ := M'.toCoxeterSystem.exists_leftDescent_of_ne_one hw1
      set cs := M'.toCoxeterSystem
      set sw := cs.simple s * w with hsw_def
      have hsw_lt : cs.length sw < cs.length w := hs
      have h_w_eq : cs.simple s * sw = w := cs.simple_mul_simple_cancel_left s
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [h_w_eq]; exact hsw_lt
      have h1_decomp : H₁.mul (H₁.basis w) z =
        H₁.mul (H₁.basis (cs.simple s)) (H₁.mul (H₁.basis sw) z) := by
        conv_lhs => rw [← h_w_eq, ← H₁.length_up s sw hs_sw]
        rw [← H₁.gen_left_assoc]
      have h2_decomp : H₂.mul (H₁.basis w) z =
        H₂.mul (H₁.basis (cs.simple s)) (H₂.mul (H₁.basis sw) z) := by
        have : H₂.mul (H₂.basis w) z =
          H₂.mul (H₂.basis (cs.simple s)) (H₂.mul (H₂.basis sw) z) := by
          conv_lhs => rw [← h_w_eq, ← H₂.length_up s sw hs_sw]
          rw [← H₂.gen_left_assoc]
        rw [← hbs] at this
        rw [show H₂.basis (cs.simple s) = H₁.basis (cs.simple s) from (hbs _).symm,
          show H₂.basis sw = H₁.basis sw from (hbs _).symm] at this
        exact this
      rw [h1_decomp, h2_decomp]
      rw [ih sw (by omega) z]
      exact H₁.mul_gen_eq H₂ h_basis h_add h_smul h_sc s _

end HeckeAlgebra


-- created on 2026-10-23
-- updated on 2026-10-24
