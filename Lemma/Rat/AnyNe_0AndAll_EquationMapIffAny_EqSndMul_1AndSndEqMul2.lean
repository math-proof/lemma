import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false


universe u

/--
[WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] (W : WeierstrassCurve.Affine k) (hΔ : W.Δ ≠ 0)
  (x₀ y₀ : k) (h₀ : W.Equation x₀ y₀) :
  -- imply
  ∃ v : k × k, v ≠ 0 ∧
    ∀ x y : DualNumber k, x.fst = x₀ → y.fst = y₀ →
      ((W.map (algebraMap k (DualNumber k))).Equation x y ↔ ∃ c : k, x.snd = c * v.1 ∧ y.snd = c * v.2) := by
  -- proof
  classical
  obtain ⟨-, hgrad⟩ := (W.nonsingular_iff' x₀ y₀).mp ((W.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp h₀)
  refine ⟨(2 * y₀ + W.a₁ * x₀ + W.a₃, -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))), ?_, ?_⟩
  ·
    intro h
    obtain ⟨hy, hx⟩ := Prod.mk_eq_zero.mp h
    refine Or.elim hgrad (fun h1 => h1 (neg_eq_zero.mp hx)) (fun h1 => h1 hy)
  ·
    intro x y hx hy
    subst hx hy
    have h₀' := (W.equation_iff' _ _).mp h₀
    have hiff : ∀ z : DualNumber k, z = 0 ↔ z.fst = 0 ∧ z.snd = 0 := fun z =>
      ⟨fun h => h.symm ▸ ⟨rfl, rfl⟩, fun h => TrivSqZeroExt.ext h.1 h.2⟩
    have key : (W.map (algebraMap k (DualNumber k))).toAffine.Equation x y ↔
        (W.a₁ * y.fst - (3 * x.fst ^ 2 + 2 * W.a₂ * x.fst + W.a₄)) * x.snd +
          (2 * y.fst + W.a₁ * x.fst + W.a₃) * y.snd = 0 := by
      rw [WeierstrassCurve.Affine.equation_iff', hiff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
        WeierstrassCurve.map_a₆, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_eq_mul, op_smul_eq_mul,
        pow_succ, pow_zero, one_mul, mul_zero, zero_mul, add_zero, zero_add]
      constructor
      ·
        intro hpair
        obtain ⟨_, h2⟩ := hpair
        linear_combination h2
      ·
        intro h2
        refine ⟨by linear_combination h₀', by linear_combination h2⟩
    show (W.map (algebraMap k (DualNumber k))).toAffine.Equation x y ↔ _
    rw [key]
    constructor
    ·
      intro h
      cases hgrad
      ·
        rename_i hFx
        refine ⟨-y.snd / (W.a₁ * y.fst - (3 * x.fst ^ 2 + 2 * W.a₂ * x.fst + W.a₄)), ?_, ?_⟩
        ·
          rw [div_mul_eq_mul_div, eq_div_iff hFx]
          linear_combination h
        ·
          rw [div_mul_eq_mul_div, eq_div_iff hFx]
          ring
      ·
        rename_i hFy
        refine ⟨x.snd / (2 * y.fst + W.a₁ * x.fst + W.a₃), ?_, ?_⟩
        · refine (div_mul_cancel₀ _ hFy).symm
        ·
          rw [div_mul_eq_mul_div, eq_div_iff hFy]
          linear_combination h
    ·
      intro hpair
      obtain ⟨c, h1, h2⟩ := hpair
      rw [h1, h2]
      ring


-- created on 2026-10-20
