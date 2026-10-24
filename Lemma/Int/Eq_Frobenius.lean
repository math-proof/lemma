import Mathlib
import sympy.Basic
open WittVector


private lemma eq_zero_of_forall_pow_dvd
  {p : ℕ}
  [Fact p.Prime]
  {R : Type u}
  [CommRing R]
  [CharP R p]
  (x : WittVector p R) (h : ∀ N : ℕ, ((p : WittVector p R) ^ N) ∣ x) : x = 0 := by
  ext i
  obtain ⟨y, hy⟩ := h (i + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero y (Nat.lt_succ_self i), WittVector.zero_coeff]

private lemma sub_coeff_zero
  {p : ℕ}
  [Fact p.Prime]
  {R : Type u}
  [CommRing R]
  [CharP R p]
  (x y : WittVector p R) : (x - y).coeff 0 = x.coeff 0 - y.coeff 0 := by
  have h := WittVector.add_coeff_zero (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

private lemma pow_coeff_zero
  {p : ℕ}
  [Fact p.Prime]
  {R : Type u}
  [CommRing R]
  [CharP R p]
  (x : WittVector p R) (n : ℕ) : (x ^ n).coeff 0 = x.coeff 0 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, WittVector.one_coeff_zero]
  | succ n ih => rw [pow_succ, pow_succ, WittVector.mul_coeff_zero, ih]

private lemma exists_eq_p_mul_of_coeff_zero
  {p : ℕ}
  [Fact p.Prime]
  {R : Type u}
  [CommRing R]
  [CharP R p]
  [PerfectRing R p]
  (y : WittVector p R) (hy : y.coeff 0 = 0) :
  ∃ z : WittVector p R, y = (p : WittVector p R) * z := by
  have hV : y = verschiebung (y.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := y) (n := 1) (fun i hi => by
      have : i = 0 := by omega
      subst this; exact hy)
    simpa using this
  obtain ⟨z, hz⟩ := (WittVector.frobenius_bijective p R).2 (y.shift 1)
  refine ⟨z, ?_⟩
  rw [hV, ← hz, WittVector.verschiebung_frobenius, mul_comm]

private lemma exists_eq_teichmuller_add
  {p : ℕ}
  [Fact p.Prime]
  {R : Type u}
  [CommRing R]
  [CharP R p]
  [PerfectRing R p]
  (x : WittVector p R) :
  ∃ z : WittVector p R, x = teichmuller p (x.coeff 0) + (p : WittVector p R) * z := by
  obtain ⟨z, hz⟩ := exists_eq_p_mul_of_coeff_zero (x - teichmuller p (x.coeff 0))
    (by rw [sub_coeff_zero, WittVector.teichmuller_coeff_zero, sub_self])
  exact ⟨z, by rw [← hz, add_sub_cancel]⟩

private lemma exists_mem_closure_add_pow_mul
  {p : ℕ}
  [Fact p.Prime]
  {R : Type u}
  [CommRing R]
  [CharP R p]
  [PerfectRing R p]
  (N : ℕ) (x : WittVector p R) :
  ∃ y ∈ Subring.closure (Set.range (teichmuller p : R → WittVector p R)), ∃ z : WittVector p R,
    x = y + (p : WittVector p R) ^ N * z := by
  induction N generalizing x with
  | zero => exact ⟨0, Subring.zero_mem _, x, by simp⟩
  | succ N ih =>
      obtain ⟨x', hx'⟩ := exists_eq_teichmuller_add x
      obtain ⟨y, hy, z, hz⟩ := ih x'
      refine ⟨teichmuller p (x.coeff 0) + (p : WittVector p R) * y, ?_, z, ?_⟩
      ·
        exact Subring.add_mem _ (Subring.subset_closure ⟨_, rfl⟩)
        (Subring.mul_mem _ (natCast_mem _ p) hy)
      ·
        calc
          _ = teichmuller p (x.coeff 0) + (p : WittVector p R) * x' := hx'
          _ = _ := by rw [hz]; ring

private lemma apply_teichmuller_eq
  {p : ℕ}
  [Fact p.Prime]
  {F : Type u}
  [Field F]
  [Finite F]
  [CharP F p]
  {k : Type v}
  [CommRing k]
  [CharP k p]
  [PerfectRing k p]
  (ι : WittVector p F →+* WittVector p k) (z : F) :
  ι (teichmuller p z) = teichmuller p ((ι (teichmuller p z)).coeff 0) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨d, -, hcard⟩ := FiniteField.card F p
  set q : ℕ := Fintype.card F with hq
  set w : WittVector p k := ι (teichmuller p z) with hw
  set w₀ : k := w.coeff 0 with hw₀
  have hwq : w ^ q = w := by
    rw [hw, ← map_pow, ← map_pow, FiniteField.pow_card]
  have hw₀q : w₀ ^ q = w₀ := by rw [hw₀, ← pow_coeff_zero, hwq]
  have hwqn : ∀ n : ℕ, w ^ q ^ n = w := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_one]
    | succ n ih => rw [pow_succ, pow_mul, ih, hwq]
  have hw₀qn : ∀ n : ℕ, w₀ ^ q ^ n = w₀ := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_one]
    | succ n ih => rw [pow_succ, pow_mul, ih, hw₀q]
  have hdvd : (p : WittVector p k) ∣ w - teichmuller p w₀ := by
    obtain ⟨y, hy⟩ := exists_eq_p_mul_of_coeff_zero (w - teichmuller p w₀)
      (by rw [sub_coeff_zero, WittVector.teichmuller_coeff_zero, sub_self])
    exact ⟨y, hy⟩
  have hdvdn : ∀ n : ℕ, (p : WittVector p k) ^ ((d : ℕ) * n + 1) ∣ w - teichmuller p w₀ := by
    intro n
    have h := dvd_sub_pow_of_dvd_sub hdvd ((d : ℕ) * n)
    rwa [pow_mul, ← hcard, hwqn, ← map_pow, hw₀qn] at h
  have hzero : w - teichmuller p w₀ = 0 := by
    apply eq_zero_of_forall_pow_dvd
    intro N
    refine (pow_dvd_pow _ ?_).trans (hdvdn N)
    have : (1 : ℕ) ≤ d := d.pos
    nlinarith
  refine (sub_eq_zero.1 hzero)

private lemma apply_frobenius_teichmuller
  {p : ℕ}
  [Fact p.Prime]
  {F : Type u}
  [Field F]
  [Finite F]
  [CharP F p]
  {k : Type v}
  [CommRing k]
  [CharP k p]
  [PerfectRing k p]
  (ι : WittVector p F →+* WittVector p k) (z : F) :
  ι (frobenius (teichmuller p z)) = frobenius (ι (teichmuller p z)) := by
  have hF : frobenius (teichmuller p z) = teichmuller p z ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have hk : ∀ c : k, frobenius (teichmuller p c) = teichmuller p c ^ p := by
    intro c
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [hF, map_pow, apply_teichmuller_eq ι z, hk]

private lemma helper_main
  {p : ℕ}
  [Fact p.Prime]
  {F : Type u}
  [Field F]
  [Finite F]
  [CharP F p]
  {k : Type v}
  [CommRing k]
  [CharP k p]
  [PerfectRing k p]
  (ι : WittVector p F →+* WittVector p k) (x : WittVector p F) :
  ι (frobenius x) = frobenius (ι x) := by
  set f : WittVector p F →+* WittVector p k := ι.comp frobenius with hf
  set g : WittVector p F →+* WittVector p k := (frobenius : WittVector p k →+* WittVector p k).comp ι with hg
  have hfg : Set.EqOn f g (Set.range (teichmuller p : F → WittVector p F)) := by
    rintro _ ⟨z, rfl⟩
    exact apply_frobenius_teichmuller ι z
  have hcl := RingHom.eqOn_set_closure hfg
  suffices h : f x - g x = 0 by
    have := sub_eq_zero.1 h
    simpa [hf, hg] using this
  apply eq_zero_of_forall_pow_dvd
  intro N
  obtain ⟨y, hy, z, hz⟩ := exists_mem_closure_add_pow_mul N x
  refine ⟨f z - g z, ?_⟩
  rw [hz, map_add, map_add, hcl hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  ring

universe u v in
/--
[WittVector_ringHom_map_frobenius_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WittVector_ringHom_map_frobenius_of_finite.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {F : Type u} [Field F] [Finite F] [CharP F p]
  {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p]
  {ι : WittVector p F →+* WittVector p k}
  {x : WittVector p F} :
-- imply
  ι (WittVector.frobenius x) = WittVector.frobenius (ι x) :=
-- proof
  helper_main ι x


-- created on 2026-10-23
