import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.StandardFormBridge
open SymmetricBilinearForms
open Finset


namespace SymmetricBilinearForms

/--
[sum_diagonal_ji](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/StandardFormBridge.lean)
-/
@[path]
lemma sum_diagonal_ji
  {a : ℕ}
  {i j : ℕ} :
-- imply
  (∑ x : Fin a, if (x : Fin a).val = j then (if (x : Fin a).val = i then (1 : ZMod 2) else 0) else 0) = if (i < a ∧ i = j) then 1 else 0 := by
-- proof
  have key : ∀ x : Fin a,
    (if x.val = j then (if x.val = i then (1 : ZMod 2) else 0) else 0) =
    if (x.val = i ∧ i = j) then 1 else 0 := by
    intro x; split_ifs <;> simp_all
  simp_rw [key, ite_and]
  by_cases hia : i < a
  · have heq : (∑ x : Fin a, if x.val = i then (if i = j then (1 : ZMod 2) else 0) else 0) =
    (∑ x : Fin a, if x = ⟨i, hia⟩ then (if i = j then 1 else 0) else 0) := by
    congr 1; funext x; simp [Fin.ext_iff]
    rw [heq, Finset.sum_ite_eq']; simp [hia]
  · have : (∑ x : Fin a, if x.val = i then (if i = j then (1 : ZMod 2) else 0) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro x _; simp [show x.val ≠ i from by omega]
    rw [this]; simp [hia]

end SymmetricBilinearForms

namespace SymmetricBilinearForms

/--
[sum_hyperbolic_ji](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/StandardFormBridge.lean)
-/
@[path]
lemma sum_hyperbolic_ji
  {a b : ℕ}
  {i j : ℕ}
-- given
  (_hi : i < a + 2*b)
  (hj : j < a + 2*b) :
-- imply
  (∑ x : Fin b, ((if a + 2 * x.val + 1 = j then (if a + 2 * x.val + 0 = i then (1 : ZMod 2) else 0) else 0) + (if a + 2 * x.val + 0 = j then (if a + 2 * x.val + 1 = i then (1 : ZMod 2) else 0) else 0))) = if (i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2) then 1 else 0 := by
-- proof
  have key : ∀ x : Fin b,
    (if a + 2 * x.val + 1 = j then
      (if a + 2 * x.val + 0 = i then (1 : ZMod 2) else 0) else 0) +
    (if a + 2 * x.val + 0 = j then
      (if a + 2 * x.val + 1 = i then (1 : ZMod 2) else 0) else 0) =
    if (x.val = (i - a) / 2 ∧ i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2)
      then 1 else 0 := by
    intro x; split_ifs <;> simp_all (config := { decide := true }) <;> omega
  simp_rw [key]
  split_ifs with hP
  · obtain ⟨hia, hja, hdiv, hmod⟩ := hP
    have hk : (i - a) / 2 < b := by omega
    have hsimpl : ∀ x : Fin b,
      (if (x.val = (i - a) / 2 ∧ i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2)
        then (1 : ZMod 2) else 0) =
      (if x.val = (i - a) / 2 then 1 else 0) := by
      intro x; split_ifs with h1 h2 h3 <;> simp_all
    simp_rw [hsimpl]
    have heq2 : (∑ x : Fin b, if x.val = (i - a) / 2 then (1 : ZMod 2) else 0) =
      (∑ x : Fin b, if x = ⟨(i - a) / 2, hk⟩ then 1 else 0) := by
      congr 1; funext x; simp [Fin.ext_iff]
    rw [heq2, Finset.sum_ite_eq']; simp
  · apply Finset.sum_eq_zero; intro x _
    have : ¬ (x.val = (i - a) / 2 ∧ i ≥ a ∧ j ≥ a ∧ (i - a) / 2 = (j - a) / 2 ∧ (i - a) % 2 ≠ (j - a) % 2) := by
      intro ⟨_, h2, h3, h4, h5⟩; exact hP ⟨h2, h3, h4, h5⟩
    simp [this]

end SymmetricBilinearForms

namespace SymmetricBilinearForms

/--
[standardFormF2_eq_toMatrix'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/StandardFormBridge.lean)
-/
@[path]
lemma standardFormF2_eq_toMatrix'
  {a b : ℕ} :
-- imply
  LinearMap.BilinForm.toMatrix' (LinearMap.BilinForm.congr (prodToFinEquiv a b) (BilinFormZMod2.standardF2Form a b)) = standardFormF2 a b := by
-- proof
  ext i j
  simp only [LinearMap.BilinForm.toMatrix'_apply, LinearMap.BilinForm.congr_apply,
    BilinFormZMod2.standardF2Form, LinearMap.mk₂_apply, prodToFinEquiv, LinearEquiv.coe_symm_mk]
  simp only [Pi.single_apply, Fin.ext_iff]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [Fin.val_zero, Fin.val_one]
  rw [sum_diagonal_ji a i.val j.val,
    sum_hyperbolic_ji a b i.val j.val i.isLt j.isLt]
  simp only [standardFormF2]
  split_ifs <;> first | rfl | omega
end SymmetricBilinearForms



-- created on 2026-10-23
