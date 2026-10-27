import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_pow_prime_pow_eq_self_of_aeval_int_eq_zero
  {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
  (x : k) (f : Polynomial ℤ) (hf : Polynomial.map (Int.castRingHom (ZMod p)) f ≠ 0) (hfx : Polynomial.aeval x f = 0) :
  ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by
  classical
  let _ : Algebra (ZMod p) k := ZMod.algebra k p
  have halg : IsAlgebraic (ZMod p) x := by
    refine ⟨Polynomial.map (Int.castRingHom (ZMod p)) f, hf, ?_⟩
    rw [show Int.castRingHom (ZMod p) = algebraMap ℤ (ZMod p) from (algebraMap_int_eq (ZMod p)).symm,
      Polynomial.aeval_map_algebraMap]
    refine hfx
  have hint : IsIntegral (ZMod p) x := halg.isIntegral
  let F := IntermediateField.adjoin (ZMod p) ({x} : Set k)
  let _ : FiniteDimensional (ZMod p) F := IntermediateField.adjoin.finiteDimensional hint
  let _ : Finite F := Module.finite_of_finite (ZMod p)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F p := by
    have := (algebraMap F k).charP_iff_charP p
    refine this.mpr inferInstance
  obtain ⟨n, hp', hcard⟩ := FiniteField.card F p
  refine ⟨(n : ℕ), n.pos, ?_⟩
  have hxF : x ∈ F := IntermediateField.subset_adjoin _ _ (Set.mem_singleton x)
  have key := FiniteField.pow_card (⟨x, hxF⟩ : F)
  rw [hcard] at key
  have this := congrArg (fun y : F => (y : k)) key
  simp at this
  refine this
/--
[ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField.lean)
-/
@[path]
private lemma main
  [Field L] [CharZero L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L)
  (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField ↥A) p] :
  -- imply
  ∀ x : IsLocalRing.ResidueField ↥A, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by
  -- proof
  classical
  intro x
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x
  subst ha
  have haQ : IsAlgebraic ℚ (a : L) := Algebra.IsAlgebraic.isAlgebraic _
  have haZ : IsAlgebraic ℤ (a : L) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr haQ
  obtain ⟨f₀, hf₀, hf₀a⟩ := haZ
  set f := f₀.primPart with hfdef
  have hfprim : f.IsPrimitive := f₀.isPrimitive_primPart
  have hfa : Polynomial.aeval (a : L) f = 0 := by
    have h := hf₀a
    rw [f₀.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C] at h
    cases mul_eq_zero.mp h
    ·
      rename_i hcontent
      rw [eq_intCast, Int.cast_eq_zero] at hcontent
      refine absurd hcontent (fun hc => hf₀ (Polynomial.content_eq_zero_iff.mp hc))
    ·
      rename_i hzero
      refine hzero
  have hfaA : Polynomial.aeval a f = 0 := by
    apply Subtype.val_injective
    have : ((Polynomial.aeval a f : ↥A) : L) = Polynomial.aeval (a : L) f := by
      rw [show ((a : ↥A) : L) = algebraMap ↥A L a from rfl, Polynomial.aeval_algebraMap_apply]
      rfl
    rw [this, hfa]
    rfl
  have hfx : Polynomial.aeval (IsLocalRing.residue ↥A a) f = 0 := by
    have h1 : Polynomial.aeval (IsLocalRing.residue ↥A a) f = IsLocalRing.residue ↥A (Polynomial.aeval a f) :=
      Polynomial.aeval_algHom_apply ((IsLocalRing.residue ↥A).toIntAlgHom) a f
    rw [h1, hfaA, map_zero]
  have hfbar : Polynomial.map (Int.castRingHom (ZMod p)) f ≠ 0 := by
    intro h0
    apply (Nat.Prime.ne_one Fact.out : p ≠ 1)
    have hdvd : ∀ i, (p : ℤ) ∣ f.coeff i := fun i => by
      have := congrArg (fun g => Polynomial.coeff g i) h0
      simp only [Polynomial.coeff_map, Int.coe_castRingHom, Polynomial.coeff_zero] at this
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
    have h1 : IsUnit ((p : ℤ)) := hfprim (p : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd)
    cases Int.isUnit_iff.mp h1
    ·
      rename_i hpunit
      exact_mod_cast hpunit
    ·
      rename_i hneg
      refine absurd hneg ?_
      have := (Fact.out : p.Prime).pos
      omega
  refine exists_pow_prime_pow_eq_self_of_aeval_int_eq_zero p _ f hfbar hfx


-- created on 2026-10-20
