import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq.lean)
-/
@[path]
private lemma main
  (k : Type) [Field k] [IsAlgClosed k]
  (ℓ : ℕ) [Fact ℓ.Prime]
  -- given
  (hℓ : (ℓ : k) ≠ 0) :
  -- imply
  ∃ ζ : ℕ → k, (∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n := by
  -- proof
  classical
  have hℓp : ℓ.Prime := Fact.out
  let _ : NeZero (ℓ : k) := ⟨hℓ⟩
  obtain ⟨ζ₁, hζ₁⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k ℓ
  have hroot : ∀ x : k, ∃ z : k, z ^ ℓ = x := fun x => IsAlgClosed.exists_pow_nat_eq x hℓp.pos
  choose step hstep using hroot
  let ζ : ℕ → k := fun n => Nat.rec (motive := fun _ => k) 1 (fun m z => if m = 0 then ζ₁ else step z) n
  have hζ0 : ζ 0 = 1 := rfl
  have hζs : ∀ n : ℕ, ζ (n + 1) = if n = 0 then ζ₁ else step (ζ n) := fun n => rfl
  have hcompat : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n := by
    intro n
    rw [hζs]
    split_ifs with h
    ·
      subst h
      rw [hζ0]
      apply hζ₁.pow_eq_one
    · apply hstep _
  have hprim : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [hζ0, pow_zero]
      apply IsPrimitiveRoot.one
    | succ n ih =>
      cases n with
      | zero =>
        rw [hζs, ite_eq_left rfl, zero_add, pow_one]
        apply hζ₁
      | succ n =>
        have hω : ζ (n + 2) ^ ℓ = ζ (n + 1) := hcompat (n + 1)
        have hη : IsPrimitiveRoot (ζ (n + 2) ^ ℓ ^ (n + 1)) ℓ := by
          have h' : ζ (n + 2) ^ ℓ ^ (n + 1) = ζ (n + 1) ^ ℓ ^ n := by
            rw [← hω, ← pow_mul, ← pow_succ']
          rw [h']
          apply ih.pow (pow_pos hℓp.pos _) (pow_succ ℓ n)
        rw [IsPrimitiveRoot.iff_def]
        refine ⟨?_, fun l hl => ?_⟩
        · rw [pow_succ, pow_mul, hη.pow_eq_one]
        ·
          have h1 : ℓ ^ (n + 1) ∣ l := by
            rw [← ih.pow_eq_one_iff_dvd, ← hω, ← pow_mul, mul_comm, pow_mul, hl, one_pow]
          obtain ⟨t, rfl⟩ := h1
          rw [pow_mul] at hl
          have h2 : ℓ ∣ t := (hη.pow_eq_one_iff_dvd t).1 hl
          rw [pow_succ]
          apply Nat.mul_dvd_mul_left _ h2
  refine ⟨ζ, hprim, hcompat⟩


-- created on 2026-10-20
-- updated on 2026-10-28
