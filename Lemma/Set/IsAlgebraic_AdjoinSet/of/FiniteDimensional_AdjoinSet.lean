import Mathlib
import sympy.Basic


/--
[Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsAlgebraic_adjoin_singleton_of_finiteDimensional_intermediateField_adjoin_of_isFractionRing.lean)
-/
@[path]
private lemma main
  {R K F : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Field F] [Algebra R F] [Algebra K F] [IsScalarTower R K F]
  {g : F}
-- given
  (hFD : FiniteDimensional ↥(IntermediateField.adjoin K ({g} : Set F)) F) :
-- imply
  Algebra.IsAlgebraic ↥(Algebra.adjoin R ({g} : Set F)) F := by
-- proof
  classical
  let S : Subalgebra R F := Algebra.adjoin R ({g} : Set F)
  let E : IntermediateField K F := IntermediateField.adjoin K ({g} : Set F)
  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K F]
    apply (algebraMap K F).injective.comp (IsFractionRing.injective R K)
  have hSE : ∀ s : F, s ∈ S → s ∈ E := by
    intro s hs
    have hle : S ≤ E.toSubalgebra.restrictScalars R :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self K g))
    refine hle hs
  have hfrac : ∀ z : F, z ∈ E → ∃ a b : F, a ∈ S ∧ b ∈ S ∧ b ≠ 0 ∧ z * b = a := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      refine ⟨x, 1, Algebra.subset_adjoin hx, one_mem _, one_ne_zero, mul_one _⟩
    | algebraMap k =>
      obtain ⟨x, y, hy, hk⟩ := IsFractionRing.div_surjective (A := R) k
      have hy0 : algebraMap R F y ≠ 0 := fun h => nonZeroDivisors.ne_zero hy (hRF (by rw [h, map_zero]))
      refine ⟨algebraMap R F x, algebraMap R F y, Subalgebra.algebraMap_mem _ _, Subalgebra.algebraMap_mem _ _, hy0, ?_⟩
      rw [← hk, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_mul_cancel₀ _ hy0]
    | add x y hx hy ihx ihy =>
      obtain ⟨a₁, b₁, ha₁, hb₁, hb₁0, h₁⟩ := ihx
      obtain ⟨a₂, b₂, ha₂, hb₂, hb₂0, h₂⟩ := ihy
      refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, add_mem (mul_mem ha₁ hb₂) (mul_mem ha₂ hb₁), mul_mem hb₁ hb₂, mul_ne_zero hb₁0 hb₂0, ?_⟩
      rw [← h₁, ← h₂]
      ring
    | inv x hx ihx =>
      obtain ⟨a, b, ha, hb, hb0, h⟩ := ihx
      if ha0 : a = 0 then
        have hx0 : x = 0 := by
          obtain h' | h' := mul_eq_zero.mp (h.trans ha0)
          · apply h'
          · apply absurd h' hb0
        refine ⟨0, 1, zero_mem _, one_mem _, one_ne_zero, ?_⟩
        rw [hx0, inv_zero, zero_mul]
      else
        have hx0 : x ≠ 0 := by
          intro hx0
          apply ha0
          rw [← h, hx0, zero_mul]
        refine ⟨b, a, hb, ha, ha0, ?_⟩
        rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
    | mul x y hx hy ihx ihy =>
      obtain ⟨a₁, b₁, ha₁, hb₁, hb₁0, h₁⟩ := ihx
      obtain ⟨a₂, b₂, ha₂, hb₂, hb₂0, h₂⟩ := ihy
      refine ⟨a₁ * a₂, b₁ * b₂, mul_mem ha₁ ha₂, mul_mem hb₁ hb₂, mul_ne_zero hb₁0 hb₂0, ?_⟩
      rw [← h₁, ← h₂]
      ring
  let _ : Algebra ↥S ↥E :=
    ((S.val : ↥S →ₐ[R] F).toRingHom.codRestrict E.toSubring (fun s => hSE s.1 s.2)).toAlgebra
  have halgSE : ∀ s : ↥S, ((algebraMap ↥S ↥E s : ↥E) : F) = (s : F) := fun _ => rfl
  have : IsScalarTower ↥S ↥E F := IsScalarTower.of_algebraMap_eq (fun s => rfl)
  have : IsFractionRing ↥S ↥E := by
    refine ⟨?_, ?_, ?_⟩
    ·
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro h0
      have : ((y : ↥S) : F) = 0 := by
        have := congrArg (fun e : ↥E => (e : F)) h0
        simp [halgSE] at this
      apply nonZeroDivisors.ne_zero y.2 (Subtype.ext this)
    ·
      intro z
      obtain ⟨a, b, ha, hb, hb0, h⟩ := hfrac (z : F) z.2
      have hb0' : (⟨b, hb⟩ : ↥S) ≠ 0 := fun h' => hb0 (congrArg Subtype.val h')
      refine ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, mem_nonZeroDivisors_of_ne_zero hb0'⟩), ?_⟩
      apply Subtype.ext
      show (z : F) * (((algebraMap ↥S ↥E) ⟨b, hb⟩ : ↥E) : F) = (((algebraMap ↥S ↥E) ⟨a, ha⟩ : ↥E) : F)
      rw [halgSE, halgSE]
      apply h
    ·
      intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : F) = (y : F) := by
        have := congrArg (fun e : ↥E => (e : F)) hxy
        rw [halgSE, halgSE] at this
        apply this
      rw [Subtype.ext this]
  have : Algebra.IsAlgebraic ↥E F := Algebra.IsAlgebraic.of_finite ↥E F
  refine ⟨fun x => ?_⟩
  apply (IsFractionRing.isAlgebraic_iff ↥S ↥E F).mpr (Algebra.IsAlgebraic.isAlgebraic x)


-- created on 2026-10-13
