import Mathlib
import sympy.Basic
import Lemma.ModularCurve.PeriodMap
open scoped MatrixGroups
open ModularCurve.Period


private lemma parabolicHoms_castAddHom_comp_eq_zero_iff
  {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
  {p : ℕ}
  (x : parabolicHoms ℤ Γ ℤ) :
  (Int.castAddHom (ZMod p)).comp (x : Additive Γ →+ ℤ) = 0
    ↔ ∃ x' : parabolicHoms ℤ Γ ℤ, x = (p : ℤ) • x' := by
  constructor
  ·
    intro h
    have hdvd : ∀ m, (p : ℤ) ∣ (x : Additive Γ →+ ℤ) m := fun m => by
      have := DFunLike.congr_fun h m
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
    have hψpar : (⟨⟨fun m => (x : Additive Γ →+ ℤ) m / (p : ℤ), by simp⟩, fun a b => by
        show (x : Additive Γ →+ ℤ) (a + b) / (p : ℤ) = _ / _ + _ / _
        rw [map_add, Int.add_ediv_of_dvd_left (hdvd a)]⟩ : Additive Γ →+ ℤ)
          ∈ parabolicHoms ℤ Γ ℤ := by
      intro γ hγ
      show (x : Additive Γ →+ ℤ) (Additive.ofMul γ) / (p : ℤ) = 0
      rw [x.2 γ hγ, Int.zero_ediv]
    refine ⟨⟨_, hψpar⟩, Subtype.ext ?_⟩
    ext m
    exact (Int.mul_ediv_cancel' (hdvd m)).symm
  ·
    rintro ⟨x', rfl⟩
    ext m
    simp
/--
[LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff.lean)
-/
@[path]
private lemma main
  {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
  {p : ℕ}
  {x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ} :
-- imply
  (Int.castAddHom (ZMod p)).comp (x : Additive Γ →+ ℤ) = 0
    ↔ ∃ x' : ModularCurve.Period.parabolicHoms ℤ Γ ℤ, x = (p : ℤ) • x' :=
-- proof
  parabolicHoms_castAddHom_comp_eq_zero_iff x


-- created on 2026-10-23
