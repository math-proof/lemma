import Mathlib
import sympy.Basic
open IntermediateField
open Polynomial


/--
[IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow.lean)
-/
@[path]
private lemma main
  [Field F] [Field E] [Algebra F E]
  {m : ℕ}
  {ζ₀ : E}
  {a : ℕ}
-- given
  (hm : 0 < m)
  (hζ₀ : IsPrimitiveRoot ζ₀ m)
  (ha : a.Coprime m)
  (hroot : Polynomial.aeval (ζ₀ ^ a) (minpoly F ζ₀) = 0) :
-- imply
  ∃ φ : (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}) ≃ₐ[F] (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}),
      ∀ ζ : IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}, (ζ : E) ^ m = 1 → (φ ζ : E) = (ζ : E) ^ a := by
-- proof
  classical
    have : NeZero m := ⟨hm.ne'⟩
    have hint : IsIntegral F ζ₀ := IsIntegral.of_pow hm (by rw [hζ₀.pow_eq_one]; apply isIntegral_one)
    have hζa : IsPrimitiveRoot (ζ₀ ^ a) m := hζ₀.pow_of_coprime a ha
    have hinta : IsIntegral F (ζ₀ ^ a) := hint.pow a
    set L := IntermediateField.adjoin F {ζ : E | ζ ^ m = 1} with hLdef
    have hgen : ∀ (η : E), IsPrimitiveRoot η m → L = F⟮η⟯ := by
      intro η hη
      apply le_antisymm
      ·
        rw [hLdef, IntermediateField.adjoin_le_iff]
        intro ζ hζ
        obtain ⟨i, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hζ
        exact pow_mem (IntermediateField.mem_adjoin_simple_self F η) i
      ·
        rw [IntermediateField.adjoin_simple_le_iff, hLdef]
        exact IntermediateField.subset_adjoin F _ hη.pow_eq_one
    have h1 : L = F⟮ζ₀⟯ := hgen ζ₀ hζ₀
    have h2 : L = F⟮ζ₀ ^ a⟯ := hgen _ hζa
    have hmin : minpoly F ζ₀ = minpoly F (ζ₀ ^ a) :=
      minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
    let pb₁ := IntermediateField.adjoin.powerBasis hint
    let pb₂ := IntermediateField.adjoin.powerBasis hinta
    have hpb : minpoly F pb₁.gen = minpoly F pb₂.gen := by
      rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.minpoly_gen, IntermediateField.minpoly_gen, hmin]
    let e₁ : F⟮ζ₀⟯ ≃ₐ[F] F⟮ζ₀ ^ a⟯ := pb₁.equivOfMinpoly pb₂ hpb
    have he₁ : e₁ (IntermediateField.AdjoinSimple.gen F ζ₀) = IntermediateField.AdjoinSimple.gen F (ζ₀ ^ a) := by
      have := pb₁.equivOfMinpoly_gen pb₂ hpb
      rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_gen] at this
    let φ : L ≃ₐ[F] L :=
      (IntermediateField.equivOfEq h1).trans (e₁.trans (IntermediateField.equivOfEq h2.symm))
    refine ⟨φ, fun ζ hζ => ?_⟩
    obtain ⟨i, -, hi⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
    have hcoe : (ζ : E) = ((IntermediateField.AdjoinSimple.gen F ζ₀ ^ i : F⟮ζ₀⟯) : E) := by
      rw [IntermediateField.equivOfEq_apply]
      change (ζ : E) = ((IntermediateField.AdjoinSimple.gen F ζ₀ ^ i : F⟮ζ₀⟯) : E)
      rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hi]
    have hx : IntermediateField.equivOfEq h1 ζ = (IntermediateField.AdjoinSimple.gen F ζ₀) ^ i :=
      Subtype.ext hcoe
    change (((IntermediateField.equivOfEq h2.symm) (e₁ ((IntermediateField.equivOfEq h1) ζ)) : L) : E) = _
    rw [IntermediateField.equivOfEq_apply, hx, map_pow, he₁]
    change (((IntermediateField.AdjoinSimple.gen F (ζ₀ ^ a)) ^ i : F⟮ζ₀ ^ a⟯) : E) = _
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, ← hi, ← pow_mul, ← pow_mul, mul_comm]


-- created on 2026-10-23
