import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_X0
open ModularCurve IntermediateField


private lemma  algHom_ext_of_eq_on_divisorExpansions
  {N : ℕ}
  {A : Type*} [DivisionRing A] [Algebra ℚ A]
  {f g : modularFunctionFieldFull N →ₐ[ℚ] A}
  (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), f ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩ = g ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩) :
  f = g := by
  ext ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hxS =>
      obtain ⟨d, hd, hdN, rfl⟩ := hxS
      exact h d hd hdN
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
          (modularFunctionFieldFull N).algebraMap_mem r⟩ : modularFunctionFieldFull N) = algebraMap ℚ (modularFunctionFieldFull N) r := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r = ((algebraMap ℚ (modularFunctionFieldFull N) r : modularFunctionFieldFull N) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r, eq_ratCast (algebraMap ℚ (modularFunctionFieldFull N)) r]
        norm_cast
      exact (congrArg f hr).trans ((f.commutes r).trans ((g.commutes r).symm.trans (congrArg g hr.symm)))
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) = g (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]
/--
[ModularCurve_modularFunctionFieldFull_algHom_ext](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_modularFunctionFieldFull_algHom_ext.lean)
-/
@[path]
private lemma main
  [DivisionRing A] [Algebra ℚ A]
  {N : ℕ}
  {f g : modularFunctionFieldFull N →ₐ[ℚ] A}
-- given
  (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), f ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩ = g ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩) :
-- imply
  f = g :=
-- proof
  algHom_ext_of_eq_on_divisorExpansions h


-- created on 2026-10-23
