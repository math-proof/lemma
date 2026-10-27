import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[TensorProduct_exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TensorProduct_exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime] [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Field K] [Algebra (ZMod p) K] [AddCommGroup W] [Module K W] [Module (ZMod p) W] [IsScalarTower (ZMod p) K W]
  (Θ : V →ₗ[ZMod p] W)
  -- given
  (hcard : Nat.card V = p ^ Module.finrank K (Submodule.span K (Set.range Θ))) :
  -- imply
  ∃ e : TensorProduct (ZMod p) K V ≃ₗ[K] Submodule.span K (Set.range Θ), ∀ (c : K) (v : V), (e (TensorProduct.tmul (ZMod p) c v) : W) = c • Θ v := by
  -- proof
  classical
  let Φ : TensorProduct (ZMod p) K V →ₗ[K] W := Θ.liftBaseChange K
  have hrange : LinearMap.range Φ = Submodule.span K (Set.range Θ) := by
    rw [LinearMap.range_liftBaseChange, LinearMap.coe_range]
  let _ : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let _ : FiniteDimensional K (Submodule.span K (Set.range Θ)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range Θ)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdim : Module.finrank K (TensorProduct (ZMod p) K V) = Module.finrank K (Submodule.span K (Set.range Θ)) := by
    rw [Module.finrank_baseChange]
    apply Nat.pow_right_injective hp
    simp only
    rw [← hcard, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  let Ψ : TensorProduct (ZMod p) K V →ₗ[K] (Submodule.span K (Set.range Θ)) :=
    LinearMap.codRestrict _ Φ (fun x => hrange ▸ LinearMap.mem_range_self Φ x)
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨w, hw⟩
    rw [← hrange] at hw
    obtain ⟨x, rfl⟩ := hw
    refine ⟨x, rfl⟩
  have hinj : Function.Injective Ψ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  refine ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun c v => ?_⟩
  show Φ (TensorProduct.tmul (ZMod p) c v) = c • Θ v
  apply LinearMap.liftBaseChange_tmul K Θ c v


-- created on 2026-10-20
