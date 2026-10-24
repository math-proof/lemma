import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


variable [Field E]
variable {p : ℕ} [Fact p.Prime] [CharP E p]

private noncomputable def En (n : ℕ) : Subfield E := Subfield.map (iterateFrobenius E p n) ⊤

private lemma En_zero :
  -- imply
  En 0 = (⊤ : Subfield E) := by
  -- proof
  ext x
  simp only [En, iterateFrobenius_zero, Subfield.mem_map, RingHom.id_apply, Subfield.mem_top,
    true_and, exists_eq]

private lemma En_succ
  {n : ℕ} :
  -- imply
  En (n + 1) = Subfield.map (frobenius E p) (En n) := by
  -- proof
  rw [En, En, Subfield.map_map, ← iterateFrobenius_one, ← iterateFrobenius_add, Nat.add_comm]

private lemma En_one :
  -- imply
  En 1 = (frobenius E p).fieldRange := by
  -- proof
  rw [En, iterateFrobenius_one, RingHom.fieldRange_eq_map]

private lemma map_frobenius_le
  {S : Subfield E} :
  -- imply
  Subfield.map (frobenius E p) S ≤ S := by
  -- proof
  intro _ hx
  obtain ⟨x, hx, rfl⟩ := hx
  rw [frobenius_def]
  apply pow_mem hx

private lemma En_exponent_le
  {S : Subfield E} [IsPurelyInseparable S E] [FiniteDimensional S E] :
  -- imply
  En (IsPurelyInseparable.exponent S E) ≤ S := by
  -- proof
  intro _ hx
  obtain ⟨x, -, rfl⟩ := hx
  rw [iterateFrobenius_def]
  obtain ⟨y, hy⟩ := RingHom.mem_range.1 (IsPurelyInseparable.exponent_def' S p x)
  rw [← hy]
  apply y.2

private lemma le_En_one
  {S : Subfield E} [IsPurelyInseparable S E] [FiniteDimensional S E]
  -- given
  (hp : Module.finrank (frobenius E p).fieldRange E = p)
  (hS : S ≠ ⊤) :
  -- imply
  S ≤ En 1 := by
  -- proof
  have hprime : p.Prime := Fact.out
  have hE1top : Subfield.relfinrank (En 1) (⊤ : Subfield E) = p := by
    rw [Subfield.relfinrank_top_right, En_one]
    apply hp
  have hmul := Subfield.relfinrank_mul_relfinrank
    (le_sup_left : En 1 ≤ En 1 ⊔ S) (le_top : En 1 ⊔ S ≤ ⊤)
  rw [hE1top] at hmul
  have hdvd : (En 1 ⊔ S).relfinrank ⊤ ∣ p := Dvd.intro_left _ hmul
  obtain h1 | h2 := (Nat.dvd_prime hprime).1 hdvd
  ·
    exfalso
    have htop : (⊤ : Subfield E) ≤ En 1 ⊔ S := Subfield.relfinrank_eq_one_iff.1 h1
    let key : ∀ n : ℕ, (⊤ : Subfield E) ≤ En n ⊔ S := fun n => by
      induction n
      ·
        rw [En_zero]
        apply le_sup_left
      ·
        rename_i n ih
        have hmono : Subfield.map (frobenius E p) ⊤ ≤
          Subfield.map (frobenius E p) (En n ⊔ S) :=
          (Subfield.gc_map_comap (frobenius E p)).monotone_l ih
        rw [Subfield.map_sup, ← En_succ] at hmono
        apply htop.trans
        apply sup_le
        ·
          rw [En_one, RingHom.fieldRange_eq_map]
          apply hmono.trans (sup_le_sup_left (map_frobenius_le (S := S)) _)
        · apply le_sup_right
    apply hS (top_le_iff.1 ((key (IsPurelyInseparable.exponent S E)).trans
      (sup_le (En_exponent_le (S := S)) le_rfl)))
  ·
    rw [h2] at hmul
    apply le_sup_right.trans (Subfield.relfinrank_eq_one_iff.1
      (Nat.eq_of_mul_eq_mul_right hprime.pos (by rw [hmul, one_mul])))

private lemma core
  -- given
  (hp : Module.finrank (frobenius E p).fieldRange E = p) :
  -- imply
  ∀ (d : ℕ) (S : Subfield E), IsPurelyInseparable S E → FiniteDimensional S E →
    Module.finrank S E = d → ∃ r : ℕ, d = p ^ r ∧ S = En r := by
  -- proof
  have hprime : p.Prime := Fact.out
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih S hPI hFD hd
  if hS : S = ⊤ then
    subst hS
    refine ⟨0, ?_, (En_zero).symm⟩
    rw [← hd, pow_zero, ← Subfield.relfinrank_top_right, Subfield.relfinrank_self]
  else
    have hle : S ≤ En 1 := le_En_one hp hS
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Subfield E, S₁ = Subfield.comap (frobenius E p) S := ⟨_, rfl⟩
    have hmap : Subfield.map (frobenius E p) S₁ = S := by
      rw [hS₁]
      apply Subfield.map_comap_eq_self
      rw [← En_one]
      apply hle
    have hrel : Module.finrank S E = Module.finrank S₁ E * p := by
      rw [← Subfield.relfinrank_top_right, ← Subfield.relfinrank_top_right,
        ← Subfield.relfinrank_mul_relfinrank hle le_top]
      congr 1
      · rw [En, iterateFrobenius_one, ← hmap, Subfield.relfinrank_map_map]
      ·
        rw [Subfield.relfinrank_top_right, En_one]
        apply hp
    have hpos : 0 < Module.finrank S E := Module.finrank_pos
    have hpos₁ : 0 < Module.finrank S₁ E := by
      obtain h | h := Nat.eq_zero_or_pos (Module.finrank S₁ E)
      ·
        rw [h, zero_mul] at hrel
        omega
      · apply h
    let _ : FiniteDimensional S₁ E := Module.finite_of_finrank_pos hpos₁
    let _ : IsPurelyInseparable S₁ E := by
      rw [isPurelyInseparable_iff_pow_mem S₁ p]
      intro x
      obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem S p x
      obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
      refine ⟨n + 1, RingHom.mem_range.2 ⟨⟨_, ?_⟩, rfl⟩⟩
      rw [hS₁, Subfield.mem_comap, frobenius_def]
      rw [pow_succ p n, ← pow_mul x (p ^ n) p, ← hy]
      apply pow_mem (pow_mem y.2 p)
    have hlt : Module.finrank S₁ E < d := by
      rw [← hd, hrel]
      have := (Nat.mul_lt_mul_left hpos₁).2 hprime.one_lt
      rwa [mul_one] at this
    obtain ⟨r, hr, hS₁r⟩ := ih _ hlt S₁ ‹_› ‹_› rfl
    refine ⟨r + 1, ?_, ?_⟩
    · rw [← hd, hrel, hr, pow_succ]
    · rw [← hmap, hS₁r, En_succ]

private lemma helper_main
  {M E : Type} [Field M] [Field E] [Algebra M E] [FiniteDimensional M E] [IsPurelyInseparable M E]
  {p : ℕ} [Fact p.Prime] [CharP E p]
  -- given
  (hp : Module.finrank (frobenius E p).fieldRange E = p) :
  -- imply
  ∃ r : ℕ, Module.finrank M E = p ^ r ∧
    (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange := by
  -- proof
  let _ : CharP M p := (Algebra.charP_iff M E p).2 inferInstance
  have hfr : Module.finrank M E = Module.finrank (algebraMap M E).fieldRange E := by
    refine Algebra.finrank_eq_of_equiv_equiv
      (RingHom.rangeRestrictFieldEquiv (algebraMap M E)) (RingEquiv.refl E) ?_
    ext x
    rfl
  let _ : FiniteDimensional (algebraMap M E).fieldRange E :=
    Module.finite_of_finrank_pos (hfr ▸ Module.finrank_pos)
  let _ : IsPurelyInseparable (algebraMap M E).fieldRange E := by
    rw [isPurelyInseparable_iff_pow_mem (algebraMap M E).fieldRange p]
    intro x
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem M p x
    obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
    exact ⟨n, RingHom.mem_range.2 ⟨⟨x ^ p ^ n, RingHom.mem_fieldRange.2 ⟨y, hy⟩⟩, rfl⟩⟩
  obtain ⟨r, hr, hR⟩ := core hp _ (algebraMap M E).fieldRange ‹_› ‹_› rfl
  exact ⟨r, hfr.trans hr, hR.trans (by rw [En, RingHom.fieldRange_eq_map])⟩

/--
[Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable.lean)
-/
@[path]
private lemma main
  {M E : Type} [Field M] [Field E] [Algebra M E] [FiniteDimensional M E] [IsPurelyInseparable M E]
  {p : ℕ} [Fact p.Prime] [CharP E p]
  -- given
  (hp : Module.finrank (frobenius E p).fieldRange E = p) :
  -- imply
  ∃ r : ℕ, Module.finrank M E = p ^ r ∧
    (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange := by
  -- proof
  apply helper_main hp


-- created on 2026-10-20
