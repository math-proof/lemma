import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


private lemma exists_isPrimitiveRoot
  (q : ℕ) [NeZero q] :
  ∃ μ : AlgebraicClosure ℚ, IsPrimitiveRoot μ q := by
  have hdeg : (cyclotomic q (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (cyclotomic q (AlgebraicClosure ℚ)) hdeg
  exact ⟨μ, (isRoot_cyclotomic_iff).mp hμ⟩

private noncomputable def zeta (q : ℕ) [NeZero q] : AlgebraicClosure ℚ :=
  (exists_isPrimitiveRoot q).choose

private lemma zeta_spec (q : ℕ) [NeZero q] : IsPrimitiveRoot (zeta q) q :=
  (exists_isPrimitiveRoot q).choose_spec

private noncomputable def cyc (q : ℕ) :
  (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ :=
  if h : q = 0 then 1 else
    have : NeZero q := ⟨h⟩
    (zeta_spec q).autToPow ℚ

private lemma cyc_of_ne_zero (q : ℕ) [hq : NeZero q] :
  cyc q = (zeta_spec q).autToPow ℚ := by
  unfold cyc
  rw [dite_eq_right (NeZero.ne q)]

private lemma cyc_main :
  ∃ cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ),
      ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
        μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val) := by
  refine ⟨cyc, fun q hq σ μ hμ => ?_⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hζ := zeta_spec q
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  have hspec : zeta q ^ ((hζ.autToPow ℚ σ : ZMod q).val) = σ (zeta q) := hζ.autToPow_spec ℚ σ
  rw [cyc_of_ne_zero, map_pow, ← hspec, ← pow_mul, ← pow_mul, mul_comm]


/-- [AlgebraicClosure_exists_cycloChar_family](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_exists_cycloChar_family.lean) -/
@[path]
private lemma main :
-- imply
  ∃ cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ),
    ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val) := by
-- proof
  apply cyc_main


-- created on 2026-10-13
