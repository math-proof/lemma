import Mathlib
import Initialize.Tactic.Attr.Basic


private def K
  {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] (I : Ideal R) (k : ℕ) :
  Submodule R A :=
  (I ^ k) • ⊤


private lemma K_zero
  {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] (I : Ideal R) :
-- imply
  K I (A := A) 0 = ⊤ := by
-- proof
  rw [K, pow_zero, Ideal.one_eq_top, Submodule.top_smul]


private lemma K_one
  {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] (I : Ideal R) :
-- imply
  K I (A := A) 1 = (I.map (algebraMap R A)).restrictScalars R := by
-- proof
  rw [K, pow_one, Ideal.smul_top_eq_map]


private lemma mem_K_one_iff
  {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] (I : Ideal R) (a : A) :
-- imply
  a ∈ K I (A := A) 1 ↔ a ∈ I.map (algebraMap R A) := by
-- proof
  rw [K_one]
  rfl


private lemma K_eq_bot_of_pow_eq_bot
  {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] (I : Ideal R) {n : ℕ}
-- given
  (hn : I ^ n = ⊥) :
-- imply
  K I (A := A) n = ⊥ := by
-- proof
  rw [K, hn, Submodule.bot_smul]


private lemma sub_mem_K_succ
  {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  (I : Ideal R) (θ : A →ₐ[R] A) {k : ℕ} {a : A}
-- given
  (hθ : ∀ a, θ a - a ∈ I.map (algebraMap R A))
  (ha : a ∈ K I k) :
-- imply
  θ a - a ∈ K I (k + 1) := by
-- proof
  rw [K] at ha
  induction ha using Submodule.smul_induction_on' with
  | smul r hr m _ =>
    have hθm : θ m - m ∈ K I (A := A) 1 := (mem_K_one_iff I _).mpr (hθ m)
    rw [K, pow_one] at hθm
    rw [map_smul, ← smul_sub, K, pow_succ, Submodule.mul_smul]
    apply Submodule.smul_mem_smul hr hθm
  | add x _ y _ hx hy =>
    have : θ (x + y) - (x + y) = (θ x - x) + (θ y - y) := by
      rw [map_add]
      ring
    rw [this]
    apply Submodule.add_mem _ hx hy


private lemma bijective_of_forall_sub_mem
  {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  (I : Ideal R) (θ : A →ₐ[R] A)
-- given
  (hI : IsNilpotent I)
  (hθ : ∀ a, θ a - a ∈ I.map (algebraMap R A)) :
-- imply
  Function.Bijective θ := by
-- proof
  obtain ⟨n, hn⟩ := hI
  have hKn : K I (A := A) n = ⊥ := K_eq_bot_of_pow_eq_bot I hn
  constructor
  ·
    intro a b hab
    have hab' : θ (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    suffices h : ∀ k, a - b ∈ K I (A := A) k by
      have := h n
      rw [hKn, Submodule.mem_bot] at this
      apply sub_eq_zero.mp this
    intro k
    induction k with
    | zero =>
      rw [K_zero]
      apply Submodule.mem_top
    | succ k ih =>
      have := sub_mem_K_succ I θ hθ ih
      rw [hab', zero_sub] at this
      apply (Submodule.neg_mem_iff _).mp this
  ·
    intro b
    suffices h : ∀ k, ∃ a, b - θ a ∈ K I (A := A) k by
      obtain ⟨a, ha⟩ := h n
      rw [hKn, Submodule.mem_bot, sub_eq_zero] at ha
      refine ⟨a, ha.symm⟩
    intro k
    induction k with
    | zero =>
      refine ⟨0, ?_⟩
      rw [K_zero]
      apply Submodule.mem_top
    | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + (b - θ a), ?_⟩
      have := sub_mem_K_succ I θ hθ ha
      have h : b - θ (a + (b - θ a)) = -(θ (b - θ a) - (b - θ a)) := by
        rw [map_add]
        ring
      rw [h]
      apply Submodule.neg_mem _ this


/--
[Algebra_FormallySmooth_exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallySmooth_exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map.lean)
-/
@[path]
private lemma main
  {A : Type v} [CommRing A]
  {A' : Type w} [CommRing A']
  {A₀ : Type x} [CommRing A₀]
  {R : Type u} [CommRing R] [Algebra R A] [Algebra R A'] [Algebra R A₀] [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R A']
  (I : Ideal R)
  (g : A →ₐ[R] A₀) (g' : A' →ₐ[R] A₀)
-- given
  (hI : IsNilpotent I)
  (hg : Function.Surjective g)
  (hg' : Function.Surjective g')
  (hkg : RingHom.ker g = I.map (algebraMap R A))
  (hkg' : RingHom.ker g' = I.map (algebraMap R A')) :
-- imply
  ∃ e : A ≃ₐ[R] A', g'.comp (e : A →ₐ[R] A') = g := by
-- proof
  have hInil : IsNilpotent I := hI
  obtain ⟨n, hn⟩ := hI
  have hnil : IsNilpotent (RingHom.ker (g : A →+* A₀)) := by
    refine ⟨n, ?_⟩
    rw [RingHom.ker_coe_toRingHom, hkg, ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    apply Ideal.zero_eq_bot.symm
  have hnil' : IsNilpotent (RingHom.ker (g' : A' →+* A₀)) := by
    refine ⟨n, ?_⟩
    rw [RingHom.ker_coe_toRingHom, hkg', ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    apply Ideal.zero_eq_bot.symm
  let φ : A →ₐ[R] A' := Algebra.FormallySmooth.liftOfSurjective g g' hg' hnil'
  have hφ : g'.comp φ = g := Algebra.FormallySmooth.comp_liftOfSurjective g g' hg' hnil'
  let ψ : A' →ₐ[R] A := Algebra.FormallySmooth.liftOfSurjective g' g hg hnil
  have hψ : g.comp ψ = g' := Algebra.FormallySmooth.comp_liftOfSurjective g' g hg hnil
  have h1 : Function.Bijective (ψ.comp φ) := by
    refine bijective_of_forall_sub_mem I _ hInil (fun a => ?_)
    rw [← hkg, RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.comp_apply]
    change (g.comp ψ) (φ a) = g a
    rw [hψ, ← AlgHom.comp_apply, hφ]
  have h2 : Function.Bijective (φ.comp ψ) := by
    refine bijective_of_forall_sub_mem I _ hInil (fun a => ?_)
    rw [← hkg', RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.comp_apply]
    change (g'.comp φ) (ψ a) = g' a
    rw [hφ, ← AlgHom.comp_apply, hψ]
  have hφbij : Function.Bijective φ :=
    ⟨Function.Injective.of_comp (f := ψ) h1.1, Function.Surjective.of_comp (g := ψ) h2.2⟩
  refine ⟨AlgEquiv.ofBijective φ hφbij, hφ⟩


-- created on 2026-10-13
