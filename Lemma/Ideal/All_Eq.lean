import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma finiteField_hom_eq_frob_pow
  {F k : Type} [Field F] [Finite F] [Field k]
  {p : ℕ} [Fact p.Prime] [CharP F p] [CharP k p]
  {σ τ : F →+* k} :
  ∃ j : ℕ, ∀ x : F, τ x = σ x ^ p ^ j := by
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  let _ : Algebra (ZMod p) k := ZMod.algebra k p
  have lift : ∀ f : F →+* k, ∃ f' : F →ₐ[ZMod p] k, ∀ x, f' x = f x := fun f =>
    ⟨{ toRingHom := f, commutes' := fun a => by
        apply RingHom.congr_fun
          (RingHom.ext_zmod (f.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) a }, fun _ => rfl⟩
  obtain ⟨σ', hσ'⟩ := lift σ
  obtain ⟨τ', hτ'⟩ := lift τ
  let _ : Module.Finite (ZMod p) F := Module.Finite.of_finite
  have hbij := FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F
  have hinj : Function.Injective
    (fun m : Fin (Module.finrank (ZMod p) F) => σ'.comp (FiniteField.frobeniusAlgHom (ZMod p) F ^ (m : ℕ))) := by
    intro i j h
    apply hbij.1
    apply AlgHom.ext
    intro x
    have := congrArg (fun g : F →ₐ[ZMod p] k => g x) h
    simp only [AlgHom.comp_apply] at this
    apply (σ' : F →+* k).injective this
  have hcard : Nat.card (F →ₐ[ZMod p] k) ≤ Nat.card (Fin (Module.finrank (ZMod p) F)) := by
    rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
    apply card_algHom_le_finrank (ZMod p) F k
  obtain ⟨m, hm⟩ := (hinj.bijective_of_nat_card_le hcard).2 τ'
  refine ⟨(m : ℕ), fun x => ?_⟩
  have := congrArg (fun g : F →ₐ[ZMod p] k => g x) hm
  simp only [AlgHom.comp_apply, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at this
  rw [← hτ', ← this, ← hσ', map_pow]
/--
[CerednikDrinfeld_exists_forall_apply_eq_apply_frobenius_zpow_of_fixed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_exists_forall_apply_eq_apply_frobenius_zpow_of_fixed.lean)
-/
@[path]
private lemma main
  {r : ℕ} [Fact r.Prime]
  {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] {π : 𝒪}
  {Onr : Type} [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
  {Fr : Onr ≃ₐ[𝒪] Onr}
  {k : Type} [Field k] [Algebra 𝒪 k]
  {ψ ψ' : Onr →ₐ[𝒪] k} {d : ℤ}
  (_ : Irreducible π)
  (_ : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
  (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
  (_ : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
  (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
  (_ : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
  (_ : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
  (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
  (hk : IsNilpotent (algebraMap 𝒪 k π))
  (hd : d ≠ 0) :
  ∃ j : ℤ, ∀ y : Onr, (Fr ^ d) y = y → ψ' y = ψ ((Fr ^ j) y) := by
  classical
  have hπk : algebraMap 𝒪 k π = 0 := hk.eq_zero
  have hrk : ((r : ℕ) : k) = 0 := by
    have hmem : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [← map_natCast (algebraMap 𝒪 k), ← hc, map_mul, hπk, mul_zero]
  let _ : CharP k r := (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).mpr hrk
  have hkill : ∀ (φ : Onr →ₐ[𝒪] k) (y : Onr), y ∈ Ideal.span {algebraMap 𝒪 Onr π} → φ y = 0 := by
    intro φ y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_mul, AlgHom.commutes, hπk, mul_zero]
  have hfrob : ∀ (φ : Onr →ₐ[𝒪] k) (y : Onr), φ (Fr y) = φ y ^ r := by
    intro φ y
    have := hkill φ _ (hFr y)
    rwa [map_sub, map_pow, sub_eq_zero] at this
  have hfrobn : ∀ (φ : Onr →ₐ[𝒪] k) (n : ℕ) (y : Onr), φ ((Fr ^ n) y) = φ y ^ r ^ n := by
    intro φ n
    induction n
    ·
      intro y
      simp
    ·
      rename_i n ih
      intro y
      rw [pow_succ', AlgEquiv.mul_apply, hfrob, ih, ← pow_mul, ← pow_succ]
  have hker : ∀ (φ φ' : Onr →ₐ[𝒪] k) (y : Onr), φ y = 0 → φ' y = 0 := by
    intro φ φ' y hy
    if hmem : y ∈ Ideal.span {algebraMap 𝒪 Onr π} then
      apply hkill φ' y hmem
    else
      obtain ⟨_, w, hw, hzw⟩ := hOnr_max.exists_inv hmem
      have h1 := hkill φ w hw
      have h2 := congrArg φ hzw
      rw [map_add, map_mul, hy, h1, map_one] at h2
      simp at h2
  obtain ⟨n, hn0, hfixn⟩ : ∃ n : ℕ, 0 < n ∧ ∀ y : Onr, (Fr ^ d) y = y → (Fr ^ n) y = y := by
    refine ⟨d.natAbs, Int.natAbs_pos.mpr hd, fun y hy => ?_⟩
    obtain h | h := Int.natAbs_eq d
    ·
      have e : (Fr ^ d) = Fr ^ d.natAbs := by
        conv_lhs => rw [h]
        rw [zpow_natCast]
      rwa [← e]
    ·
      have e : (Fr ^ d) = (Fr ^ d.natAbs)⁻¹ := by
        conv_lhs => rw [h]
        rw [zpow_neg, zpow_natCast]
      rw [e] at hy
      have := congrArg (Fr ^ d.natAbs) hy
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
      apply this.symm
  let A : Subalgebra 𝒪 Onr := AlgHom.equalizer ((Fr ^ d : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)
  have hA : ∀ y : Onr, y ∈ A ↔ (Fr ^ d) y = y := fun y => Iff.rfl
  let σ : ↥A →+* k := (ψ : Onr →+* k).comp (A.val : ↥A →+* Onr)
  let τ : ↥A →+* k := (ψ' : Onr →+* k).comp (A.val : ↥A →+* Onr)
  have hσ : ∀ a : ↥A, σ a = ψ (a : Onr) := fun _ => rfl
  have hτ : ∀ a : ↥A, τ a = ψ' (a : Onr) := fun _ => rfl
  let I : Ideal ↥A := RingHom.ker σ
  have hIτ : ∀ a : ↥A, a ∈ I → τ a = 0 := fun a ha => by
    rw [hτ]
    apply hker ψ ψ' a
    rw [← hσ]
    apply ha
  have hroot : ∀ a : ↥A, σ a ^ r ^ n = σ a := by
    intro a
    rw [hσ, ← hfrobn ψ n, hfixn a.1 ((hA a.1).mp a.2)]
  have : I.IsPrime := RingHom.ker_isPrime σ
  have hlift_inj : Function.Injective (Ideal.Quotient.lift I σ (fun a ha => ha)) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.lift_mk] at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let _ : Finite (↥A ⧸ I) := by
    let S : Set k := {x : k | x ^ r ^ n = x}
    have hSfin : S.Finite := by
      have h1 : 1 < r ^ n := Nat.one_lt_pow hn0.ne' (Fact.out : r.Prime).one_lt
      have hne : (Polynomial.X ^ (r ^ n) - Polynomial.X : Polynomial k) ≠ 0 :=
        FiniteField.X_pow_card_sub_X_ne_zero k h1
      refine ((Polynomial.X ^ (r ^ n) - Polynomial.X : Polynomial k).roots.toFinset.finite_toSet).subset ?_
      intro x hx
      have hx' : x ^ r ^ n = x := hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx', sub_self]
    let _ : Finite ↥S := hSfin.to_subtype
    refine Finite.of_injective (fun x : ↥A ⧸ I => (⟨Ideal.Quotient.lift I σ (fun a ha => ha) x, ?_⟩ : ↥S)) ?_
    ·
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.lift I σ _ (Ideal.Quotient.mk I a) ∈ S
      rw [Ideal.Quotient.lift_mk]
      apply hroot a
    ·
      intro x y hxy
      apply hlift_inj (congrArg Subtype.val hxy)
  let _ : IsDomain (↥A ⧸ I) := Ideal.Quotient.isDomain I
  let _ : I.IsMaximal := Ideal.Quotient.maximal_of_isField I (Finite.isField_of_domain (↥A ⧸ I))
  let _ : Field (↥A ⧸ I) := Ideal.Quotient.field I
  let σbar : ↥A ⧸ I →+* k := Ideal.Quotient.lift I σ (fun a ha => ha)
  let τbar : ↥A ⧸ I →+* k := Ideal.Quotient.lift I τ hIτ
  let _ : CharP (↥A ⧸ I) r := by
    apply (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).mpr
    apply hlift_inj
    rw [map_natCast, map_zero, hrk]
  obtain ⟨j, hj⟩ := finiteField_hom_eq_frob_pow (p := r) (σ := σbar) (τ := τbar)
  refine ⟨(j : ℤ), fun y hy => ?_⟩
  have := hj (Ideal.Quotient.mk I ⟨y, (hA y).mpr hy⟩)
  rw [show τbar (Ideal.Quotient.mk I ⟨y, (hA y).mpr hy⟩) = ψ' y from Ideal.Quotient.lift_mk I τ hIτ,
    show σbar (Ideal.Quotient.mk I ⟨y, (hA y).mpr hy⟩) = ψ y from Ideal.Quotient.lift_mk I σ _] at this
  rw [this, zpow_natCast, hfrobn]


-- created on 2026-10-20
