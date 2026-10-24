import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.VonSzilySuperCatalan
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[wzB_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wzB_of_nonneg (N : ℕ) (t : ℤ) (h : 0 ≤ t) :
  wzB N t = ((Nat.choose N t.toNat : ℕ) : ℚ) := by
  unfold wzB
  simp [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wzB_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wzB_neg (N : ℕ) (t : ℤ) (h : t < 0) : wzB N t = 0 := by
  have h' : ¬ (0 : ℤ) ≤ t := by omega
  unfold wzB
  simp [h']

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wzB_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wzB_gt (N : ℕ) (t : ℤ) (h : (N : ℤ) < t) : wzB N t = 0 := by
  unfold wzB
  split_ifs with h0
  · have hlt : N < t.toNat := by omega
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp
  · rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_sum_Icc_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_sum_Icc_sub (G : ℤ → ℚ) (a b : ℤ) (hab : a ≤ b + 1) :
  ∑ k ∈ Finset.Icc a b, (G (k + 1) - G k) = G (b + 1) - G a := by
  have key : ∀ n : ℤ, a - 1 ≤ n →
    ∑ k ∈ Finset.Icc a n, (G (k + 1) - G k) = G (n + 1) - G a := by
    intro n hn
    induction n, hn using Int.leInduction with
    | base =>
      have he : Finset.Icc a (a - 1) = (∅ : Finset ℤ) := by
        apply Finset.Icc_eq_empty
        omega
      rw [he, Finset.sum_empty]
      rw [sub_add_cancel, sub_self]
    | succ n hnm ih =>
      have hmem : n + 1 ∉ Finset.Icc a n := by
        simp only [Finset.mem_Icc]
        omega
      have hins : Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hins, Finset.sum_insert hmem, ih]
      ring
  exact key b (by omega)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_interior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_interior (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) (k : ℤ)
  (hk1 : max (-(M : ℤ)) (-(N : ℤ)) + 1 ≤ k) (hk2 : k ≤ min (M : ℤ) (N : ℤ) - 1) :
  ((M:ℚ)+(N:ℚ)) * ((-1:ℚ)^k * (Nat.choose (2*M) (((M:ℤ)+k).toNat) : ℚ) *
    (Nat.choose (2*N) (((N:ℤ)+k).toNat) : ℚ))
  - 2*((2:ℚ)*M-1) * ((-1:ℚ)^k * (Nat.choose (2*M-2) ((((M:ℤ)-1)+k).toNat) : ℚ) *
    (Nat.choose (2*N) (((N:ℤ)+k).toNat) : ℚ))
  = ((-1:ℚ)^((k+1)+1) * (Nat.choose (2*M-1) (((M:ℤ)-k-1).toNat) : ℚ) * (2*(N:ℚ)) *
    (Nat.choose (2*N-1) (((N:ℤ)-k-1).toNat) : ℚ))
  - ((-1:ℚ)^(k+1) * (Nat.choose (2*M-1) (((M:ℤ)-k).toNat) : ℚ) * (2*(N:ℚ)) *
    (Nat.choose (2*N-1) (((N:ℤ)-k).toNat) : ℚ)) := by
  have gMk : (0:ℤ) ≤ (M:ℤ)+k := by omega
  have gmk : (0:ℤ) ≤ ((M:ℤ)-1)+k := by omega
  have gNk : (0:ℤ) ≤ (N:ℤ)+k := by omega
  have gMk1 : (0:ℤ) ≤ (M:ℤ)-k-1 := by omega
  have gNk1 : (0:ℤ) ≤ (N:ℤ)-k-1 := by omega
  have gMk0 : (0:ℤ) ≤ (M:ℤ)-k := by omega
  have gNk0 : (0:ℤ) ≤ (N:ℤ)-k := by omega
  have h1 : (((M:ℤ)+k).toNat) ≤ 2*M := by omega
  have h2 : (((N:ℤ)+k).toNat) ≤ 2*N := by omega
  have h3 : ((((M:ℤ)-1)+k).toNat) ≤ 2*M-2 := by omega
  have h4 : (((M:ℤ)-k).toNat) ≤ 2*M-1 := by omega
  have h5 : (((N:ℤ)-k).toNat) ≤ 2*N-1 := by omega
  have h6 : (((M:ℤ)-k-1).toNat) ≤ 2*M-1 := by omega
  have h7 : (((N:ℤ)-k-1).toNat) ≤ 2*N-1 := by omega
  set a := (((M:ℤ)+k).toNat) with ha_def
  set b := (((N:ℤ)+k).toNat) with hb_def
  set c := ((((M:ℤ)-1)+k).toNat) with hc_def
  set d := (((M:ℤ)-k).toNat) with hd_def
  set e := (((N:ℤ)-k).toNat) with he_def
  set f := (((M:ℤ)-k-1).toNat) with hf_def
  set g := (((N:ℤ)-k-1).toNat) with hg_def
  have e1 := Nat.choose_eq_factorial_div_factorial h1
  have e2 := Nat.choose_eq_factorial_div_factorial h2
  have e3 := Nat.choose_eq_factorial_div_factorial h3
  have e4 := Nat.choose_eq_factorial_div_factorial h4
  have e5 := Nat.choose_eq_factorial_div_factorial h5
  have e6 := Nat.choose_eq_factorial_div_factorial h6
  have e7 := Nat.choose_eq_factorial_div_factorial h7
  rw [e1, e2, e3, e4, e5, e6, e7]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h1),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h2),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h3),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h4),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h5),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h6),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h7)]
  · field_simp
    have hac : a = c + 1 := by omega
    have hdf : d = f + 1 := by omega
    have heg : e = g + 1 := by omega
    have hsign : (-1:ℚ)^(k+1) = -(-1:ℚ)^k := by
      rw [zpow_add_one₀ (by norm_num) k]; ring
    have hsign2 : (-1:ℚ)^((k+1)+1) = (-1:ℚ)^k := by
      rw [zpow_add_one₀ (by norm_num) (k+1), hsign]; ring
    -- unify complementary factorial arguments to primary variables
    have i1 : 2*M - a = d := by omega
    have i2 : 2*M - 2 - c = f := by omega
    have i3 : 2*M - 1 - d = c := by omega
    have i4 : 2*M - 1 - f = a := by omega
    have i5 : 2*N - b = e := by omega
    have i6 : 2*N - 1 - g = b := by omega
    rw [i1, i2, i3, i4, i5, i6]
    have fa : a.factorial = (c + 1) * c.factorial := by
      conv_lhs => rw [hac]; exact Nat.factorial_succ _
    have fM1q : ((((2*M : ℕ)).factorial : ℕ):ℚ) =
      (2*(M:ℚ)) * ((2*(M:ℚ)-1)) * (((((2*M-2 : ℕ)).factorial : ℕ)):ℚ) := by
      have g1 : ((2*M : ℕ)).factorial = (2*M) * ((2*M-1)).factorial := by
        have e : 2*M = (2*M-1)+1 := by omega
        rw [e, Nat.factorial_succ, ← e]
      have g2 : ((2*M-1 : ℕ)).factorial = (2*M-1) * ((2*M-2)).factorial := by
        have e : 2*M-1 = (2*M-2)+1 := by omega
        rw [e, Nat.factorial_succ, ← e]
      have cs : ((2*M-1 : ℕ):ℚ) = 2*(M:ℚ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2*M), Nat.cast_one]
        push_cast
        ring
      rw [g1, g2]; simp only [Nat.cast_mul]; rw [cs]; ring
    have fM2 : ((((2*M-1 : ℕ)).factorial : ℕ):ℚ) =
      (2*(M:ℚ)-1) * (((((2*M-2 : ℕ)).factorial : ℕ)):ℚ) := by
      have h : ((2*M-1 : ℕ)).factorial = (2*M-1) * ((2*M-2)).factorial := by
        have e : 2*M-1 = (2*M-2)+1 := by omega
        rw [e, Nat.factorial_succ, ← e]
      have cs : ((2*M-1 : ℕ):ℚ) = 2*(M:ℚ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2*M), Nat.cast_one]
        push_cast
        ring
      rw [h, Nat.cast_mul, cs]
    have fd : d.factorial = (f + 1) * f.factorial := by
      conv_lhs => rw [hdf]; exact Nat.factorial_succ _
    have fe : e.factorial = (g + 1) * g.factorial := by
      conv_lhs => rw [heg]; exact Nat.factorial_succ _
    have fN1 : ((2*N : ℕ)).factorial = (2*N) * ((2*N-1)).factorial := by
      have e : 2*N = (2*N-1)+1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have hb1 : b = (2*N-1 - e) + 1 := by omega
    have fb1 : b.factorial = ((2*N-1 - e) + 1) * (2*N-1 - e).factorial := by
      conv_lhs => rw [hb1]; exact Nat.factorial_succ _
    rw [fa, fM1q, fd, fe, fN1, fb1, hsign, hsign2, fM2]
    -- eliminate dependent nat variables using k-free relations
    have hec : e = M + N - 1 - c := by omega
    have hgc : g = M + N - 2 - c := by omega
    have hfc : f = 2*M - 2 - c := by omega
    rw [hec, hgc, hfc]
    -- expand nat-subtraction multipliers to ℚ form
    have q1p : (((2*M-2-c+1) : ℕ):ℚ) = (2*(M:ℚ)-2-↑c)+1 := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : c ≤ 2*M-2),
        Nat.cast_sub (by omega : 2 ≤ 2*M)]
      push_cast
      ring
    have q2p : (((M+N-2-c+1) : ℕ):ℚ) = (↑M+↑N-2-↑c)+1 := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : c ≤ M+N-2),
        Nat.cast_sub (by omega : 2 ≤ M+N)]
      push_cast
      ring
    have q3p : (((2*N-1-(M+N-1-c)+1) : ℕ):ℚ) = (↑N-↑M+↑c)+1 := by
      have e0 : (((2*N-1-(M+N-1-c)) : ℕ):ℚ)
        = ((2*N-1 : ℕ):ℚ) - ((M+N-1-c : ℕ):ℚ) :=
        Nat.cast_sub (by omega)
      have e1 : (((2*N-1 : ℕ)):ℚ) = 2*(N:ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2*N)]; push_cast; ring
      have e2 : (((M+N-1-c : ℕ)):ℚ) = (↑M+↑N-1) - ↑c := by
        rw [Nat.cast_sub (by omega : c ≤ M+N-1)]
        have e3 : (((M+N-1 : ℕ)):ℚ) = (↑M+↑N) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ M+N)]; push_cast; ring
        rw [e3]
      rw [Nat.cast_add, Nat.cast_one, e0, e1, e2]; ring
    have q0p : (((c + 1 : ℕ)) : ℚ) = ↑c + 1 := by push_cast; ring
    simp only [Nat.cast_mul]
    rw [q1p, q2p, q3p, q0p]
    ring
  all_goals positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge1_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge1_key (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
  ((M : ℚ) + (N : ℚ)) * (Nat.choose (2 * N) (N + M) : ℚ)
    = 2 * (N : ℚ) * (Nat.choose (2 * N - 1) (N - M) : ℚ) := by
  have h1 : N + M ≤ 2 * N := by omega
  have h2 : N - M ≤ 2 * N - 1 := by omega
  have e1 := Nat.choose_eq_factorial_div_factorial h1
  have e2 := Nat.choose_eq_factorial_div_factorial h2
  rw [e1, e2]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h1),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h2)]
  · field_simp
    have i1 : 2 * N - (N + M) = N - M := by omega
    have i2 : 2 * N - 1 - (N - M) = N + M - 1 := by omega
    rw [i1, i2]
    have fN : (((2 * N : ℕ)).factorial : ℕ) = (2 * N) * ((2 * N - 1)).factorial := by
      have e : 2 * N = (2 * N - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have fNM : ((N + M : ℕ)).factorial = (N + M) * ((N + M - 1)).factorial := by
      have e : N + M = (N + M - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have cNM : (((N + M : ℕ)) : ℚ) = (N : ℚ) + (M : ℚ) := by push_cast; ring
    rw [fN, fNM]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [cNM]
    ring
  all_goals positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge3_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge3_key (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
  ((M : ℚ) + (N : ℚ)) * (Nat.choose (2 * N) (N - M) : ℚ)
    = 2 * (N : ℚ) * (Nat.choose (2 * N - 1) (N + M - 1) : ℚ) := by
  have h1 : N - M ≤ 2 * N := by omega
  have h2 : N + M - 1 ≤ 2 * N - 1 := by omega
  have e1 := Nat.choose_eq_factorial_div_factorial h1
  have e2 := Nat.choose_eq_factorial_div_factorial h2
  rw [e1, e2]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h1),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h2)]
  · field_simp
    have i1 : 2 * N - (N - M) = N + M := by omega
    have i2 : 2 * N - 1 - (N + M - 1) = N - M := by omega
    rw [i1, i2]
    have fN : (((2 * N : ℕ)).factorial : ℕ) = (2 * N) * ((2 * N - 1)).factorial := by
      have e : 2 * N = (2 * N - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have fNM : ((N + M : ℕ)).factorial = (N + M) * ((N + M - 1)).factorial := by
      have e : N + M = (N + M - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have cNM : (((N + M : ℕ)) : ℚ) = (N : ℚ) + (M : ℚ) := by push_cast; ring
    rw [fN, fNM]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [cNM]
    ring
  all_goals positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge2_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge2_key (M N : ℕ) (hM : 1 ≤ M) (hNM : N < M) :
  ((M : ℚ) + (N : ℚ)) * (Nat.choose (2 * M) (M + N) : ℚ)
    - 2 * (2 * (M : ℚ) - 1) * (Nat.choose (2 * M - 2) (M + N - 1) : ℚ)
    = 2 * (N : ℚ) * (Nat.choose (2 * M - 1) (M - N) : ℚ) := by
  have h1 : M + N ≤ 2 * M := by omega
  have h2 : M + N - 1 ≤ 2 * M - 2 := by omega
  have h3 : M - N ≤ 2 * M - 1 := by omega
  have e1 := Nat.choose_eq_factorial_div_factorial h1
  have e2 := Nat.choose_eq_factorial_div_factorial h2
  have e3 := Nat.choose_eq_factorial_div_factorial h3
  rw [e1, e2, e3]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h1),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h2),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h3)]
  · field_simp
    have i1 : 2 * M - (M + N) = M - N := by omega
    have i2 : 2 * M - 2 - (M + N - 1) = M - N - 1 := by omega
    have i3 : 2 * M - 1 - (M - N) = M + N - 1 := by omega
    rw [i1, i2, i3]
    have f2M : (((2 * M : ℕ)).factorial : ℕ) = (2 * M) * ((2 * M - 1)).factorial := by
      have e : 2 * M = (2 * M - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have f2M1 : (((2 * M - 1 : ℕ)).factorial : ℕ) = (2 * M - 1) * ((2 * M - 2)).factorial := by
      have e : 2 * M - 1 = (2 * M - 2) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have fMN : ((M + N : ℕ)).factorial = (M + N) * ((M + N - 1)).factorial := by
      have e : M + N = (M + N - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have fMN' : ((M - N : ℕ)).factorial = (M - N) * ((M - N - 1)).factorial := by
      have e : M - N = (M - N - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have cMN : (((M + N : ℕ)) : ℚ) = (M : ℚ) + (N : ℚ) := by push_cast; ring
    have cMN' : (((M - N : ℕ)) : ℚ) = (M : ℚ) - (N : ℚ) := by
      rw [Nat.cast_sub (by omega : N ≤ M)]
    have c2M1 : (((2 * M - 1 : ℕ)) : ℚ) = 2 * (M : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * M)]
      push_cast
      ring
    rw [f2M, f2M1, fMN, fMN']
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [cMN, cMN', c2M1]
    ring
  all_goals positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge4_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge4_key (M N : ℕ) (hM : 1 ≤ M) (hNM : N < M) :
  ((M : ℚ) + (N : ℚ)) * (Nat.choose (2 * M) (M - N) : ℚ)
    - 2 * (2 * (M : ℚ) - 1) * (Nat.choose (2 * M - 2) (M - N - 1) : ℚ)
    = 2 * (N : ℚ) * (Nat.choose (2 * M - 1) (M + N - 1) : ℚ) := by
  have h1 : M - N ≤ 2 * M := by omega
  have h2 : M - N - 1 ≤ 2 * M - 2 := by omega
  have h3 : M + N - 1 ≤ 2 * M - 1 := by omega
  have e1 := Nat.choose_eq_factorial_div_factorial h1
  have e2 := Nat.choose_eq_factorial_div_factorial h2
  have e3 := Nat.choose_eq_factorial_div_factorial h3
  rw [e1, e2, e3]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h1),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h2),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial h3)]
  · field_simp
    have i1 : 2 * M - (M - N) = M + N := by omega
    have i2 : 2 * M - 2 - (M - N - 1) = M + N - 1 := by omega
    have i3 : 2 * M - 1 - (M + N - 1) = M - N := by omega
    rw [i1, i2, i3]
    have f2M : (((2 * M : ℕ)).factorial : ℕ) = (2 * M) * ((2 * M - 1)).factorial := by
      have e : 2 * M = (2 * M - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have f2M1 : (((2 * M - 1 : ℕ)).factorial : ℕ) = (2 * M - 1) * ((2 * M - 2)).factorial := by
      have e : 2 * M - 1 = (2 * M - 2) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have fMN : ((M + N : ℕ)).factorial = (M + N) * ((M + N - 1)).factorial := by
      have e : M + N = (M + N - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have fMN' : ((M - N : ℕ)).factorial = (M - N) * ((M - N - 1)).factorial := by
      have e : M - N = (M - N - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have cMN : (((M + N : ℕ)) : ℚ) = (M : ℚ) + (N : ℚ) := by push_cast; ring
    have cMN' : (((M - N : ℕ)) : ℚ) = (M : ℚ) - (N : ℚ) := by
      rw [Nat.cast_sub (by omega : N ≤ M)]
    have c2M1 : (((2 * M - 1 : ℕ)) : ℚ) = 2 * (M : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * M)]
      push_cast
      ring
    rw [f2M, f2M1, fMN, fMN']
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [cMN, cMN', c2M1]
    ring
  all_goals positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge1 (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
  ((M : ℚ) + (N : ℚ)) * wzE M N ((M : ℤ))
    - 2 * (2 * (M : ℚ) - 1) * wzElow M N ((M : ℤ))
    = wzG M N (((M : ℤ)) + 1) - wzG M N ((M : ℤ)) := by
  have b1 : wzB (2 * M) ((M : ℤ) + (M : ℤ)) = 1 := by
    have hidx : (M : ℤ) + (M : ℤ) = ((2 * M : ℕ) : ℤ) := by push_cast; ring
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_self,
      Nat.cast_one]
  have b2 : wzB (2 * N) ((N : ℤ) + (M : ℤ))
    = ((Nat.choose (2 * N) (N + M) : ℕ) : ℚ) := by
    have hidx : (N : ℤ) + (M : ℤ) = ((N + M : ℕ) : ℤ) := by push_cast; ring
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast]
  have b3 : wzB (2 * M - 2) (((M : ℤ) - 1) + (M : ℤ)) = 0 := by
    exact wzB_gt _ _ (by omega)
  have g1 : wzB (2 * M - 1) ((M : ℤ) - ((M : ℤ) + 1)) = 0 := by
    exact wzB_neg _ _ (by omega)
  have g2 : wzB (2 * M - 1) ((M : ℤ) - (M : ℤ)) = 1 := by
    have hidx : (M : ℤ) - (M : ℤ) = ((0 : ℕ) : ℤ) := by simp
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_zero_right,
      Nat.cast_one]
  have g3 : wzB (2 * N - 1) ((N : ℤ) - (M : ℤ))
    = ((Nat.choose (2 * N - 1) (N - M) : ℕ) : ℚ) := by
    rw [wzB_of_nonneg _ _ (by omega)]
    have htn : ((N : ℤ) - (M : ℤ)).toNat = N - M := by omega
    rw [htn]
  have hsign : (-1 : ℚ) ^ ((M : ℤ) + 1) = -(-1 : ℚ) ^ (M : ℤ) := by
    rw [zpow_add_one₀ (by norm_num)]
    ring
  unfold wzE wzElow wzG
  rw [b1, b2, b3, g1, g2, g3, hsign]
  simp only [mul_one, mul_zero, zero_mul, sub_zero, zero_sub]
  linear_combination (-1 : ℚ) ^ (M : ℤ) * wz_edge1_key M N hM hMN

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge3 (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
  ((M : ℚ) + (N : ℚ)) * wzE M N ((-(M : ℤ)))
    - 2 * (2 * (M : ℚ) - 1) * wzElow M N ((-(M : ℤ)))
    = wzG M N (((-(M : ℤ))) + 1) - wzG M N ((-(M : ℤ))) := by
  have e1 : wzB (2 * M) ((M : ℤ) + (-(M : ℤ))) = 1 := by
    have hidx : (M : ℤ) + (-(M : ℤ)) = ((0 : ℕ) : ℤ) := by simp
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_zero_right,
      Nat.cast_one]
  have e2 : wzB (2 * N) ((N : ℤ) + (-(M : ℤ)))
    = ((Nat.choose (2 * N) (N - M) : ℕ) : ℚ) := by
    rw [wzB_of_nonneg _ _ (by omega)]
    have htn : ((N : ℤ) + (-(M : ℤ))).toNat = N - M := by omega
    rw [htn]
  have l1 : wzB (2 * M - 2) (((M : ℤ) - 1) + (-(M : ℤ))) = 0 := by
    exact wzB_neg _ _ (by omega)
  have h1 : wzB (2 * M - 1) ((M : ℤ) - ((-(M : ℤ)) + 1)) = 1 := by
    have hidx : (M : ℤ) - ((-(M : ℤ)) + 1) = ((2 * M - 1 : ℕ) : ℤ) := by omega
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_self,
      Nat.cast_one]
  have h2 : wzB (2 * N - 1) ((N : ℤ) - ((-(M : ℤ)) + 1))
    = ((Nat.choose (2 * N - 1) (N + M - 1) : ℕ) : ℚ) := by
    rw [wzB_of_nonneg _ _ (by omega)]
    have htn : ((N : ℤ) - ((-(M : ℤ)) + 1)).toNat = N + M - 1 := by omega
    rw [htn]
  have z1 : wzB (2 * M - 1) ((M : ℤ) - (-(M : ℤ))) = 0 := by
    exact wzB_gt _ _ (by omega)
  have hsign3 : (-1 : ℚ) ^ (((-(M : ℤ)) + 1) + 1) = (-1 : ℚ) ^ (-(M : ℤ)) := by
    rw [zpow_add_one₀ (by norm_num), zpow_add_one₀ (by norm_num)]
    ring
  unfold wzE wzElow wzG
  rw [e1, e2, l1, h1, h2, z1, hsign3]
  simp only [mul_one, mul_zero, zero_mul, sub_zero]
  linear_combination (-1 : ℚ) ^ (-(M : ℤ)) * wz_edge3_key M N hM hMN

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge2 (M N : ℕ) (hM : 1 ≤ M) (hNM : N < M) :
  ((M : ℚ) + (N : ℚ)) * wzE M N ((N : ℤ))
    - 2 * (2 * (M : ℚ) - 1) * wzElow M N ((N : ℤ))
    = wzG M N (((N : ℤ)) + 1) - wzG M N ((N : ℤ)) := by
  have e1 : wzB (2 * M) ((M : ℤ) + (N : ℤ))
    = ((Nat.choose (2 * M) (M + N) : ℕ) : ℚ) := by
    have hidx : (M : ℤ) + (N : ℤ) = ((M + N : ℕ) : ℤ) := by push_cast; ring
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast]
  have e2 : wzB (2 * N) ((N : ℤ) + (N : ℤ)) = 1 := by
    have hidx : (N : ℤ) + (N : ℤ) = ((2 * N : ℕ) : ℤ) := by push_cast; ring
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_self,
      Nat.cast_one]
  have l1 : wzB (2 * M - 2) (((M : ℤ) - 1) + (N : ℤ))
    = ((Nat.choose (2 * M - 2) (M + N - 1) : ℕ) : ℚ) := by
    rw [wzB_of_nonneg _ _ (by omega)]
    have htn : (((M : ℤ) - 1) + (N : ℤ)).toNat = M + N - 1 := by omega
    rw [htn]
  have h1 : wzB (2 * N - 1) ((N : ℤ) - ((N : ℤ) + 1)) = 0 := by
    exact wzB_neg _ _ (by omega)
  have g1 : wzB (2 * M - 1) ((M : ℤ) - (N : ℤ))
    = ((Nat.choose (2 * M - 1) (M - N) : ℕ) : ℚ) := by
    rw [wzB_of_nonneg _ _ (by omega)]
    have htn : ((M : ℤ) - (N : ℤ)).toNat = M - N := by omega
    rw [htn]
  have g2 : wzB (2 * N - 1) ((N : ℤ) - (N : ℤ)) = 1 := by
    have hidx : (N : ℤ) - (N : ℤ) = ((0 : ℕ) : ℤ) := by simp
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_zero_right,
      Nat.cast_one]
  have hsignN : (-1 : ℚ) ^ ((N : ℤ) + 1) = -(-1 : ℚ) ^ (N : ℤ) := by
    rw [zpow_add_one₀ (by norm_num)]
    ring
  unfold wzE wzElow wzG
  rw [e1, e2, l1, h1, g1, g2, hsignN]
  simp only [mul_one, mul_zero, zero_sub]
  linear_combination (-1 : ℚ) ^ (N : ℤ) * wz_edge2_key M N hM hNM

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_edge4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_edge4 (M N : ℕ) (hM : 1 ≤ M) (hNM : N < M) :
  ((M : ℚ) + (N : ℚ)) * wzE M N ((-(N : ℤ)))
    - 2 * (2 * (M : ℚ) - 1) * wzElow M N ((-(N : ℤ)))
    = wzG M N (((-(N : ℤ))) + 1) - wzG M N ((-(N : ℤ))) := by
  have e1 : wzB (2 * M) ((M : ℤ) + (-(N : ℤ)))
    = ((Nat.choose (2 * M) (M - N) : ℕ) : ℚ) := by
    rw [wzB_of_nonneg _ _ (by omega)]
    have htn : ((M : ℤ) + (-(N : ℤ))).toNat = M - N := by omega
    rw [htn]
  have e2 : wzB (2 * N) ((N : ℤ) + (-(N : ℤ))) = 1 := by
    have hidx : (N : ℤ) + (-(N : ℤ)) = ((0 : ℕ) : ℤ) := by simp
    rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_zero_right,
      Nat.cast_one]
  have l1 : wzB (2 * M - 2) (((M : ℤ) - 1) + (-(N : ℤ)))
    = ((Nat.choose (2 * M - 2) (M - N - 1) : ℕ) : ℚ) := by
    rw [wzB_of_nonneg _ _ (by omega)]
    have htn : (((M : ℤ) - 1) + (-(N : ℤ))).toNat = M - N - 1 := by omega
    rw [htn]
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · -- N = 0: both G terms vanish via the 2N factor.
    have g10 : wzG M 0 (-((0 : ℕ) : ℤ) + 1) = 0 := by
      unfold wzG
      simp
    have g00 : wzG M 0 (-((0 : ℕ) : ℤ)) = 0 := by
      unfold wzG
      simp
    have key0 := wz_edge4_key M 0 hM hNM
    unfold wzE wzElow
    rw [e1, e2, l1, g10, g00, sub_self]
    simp only [mul_one]
    linear_combination (-1 : ℚ) ^ (-((0 : ℕ) : ℤ)) * key0
  · -- N ≥ 1: standard evaluations.
    have h1 : wzB (2 * M - 1) ((M : ℤ) - ((-(N : ℤ)) + 1))
      = ((Nat.choose (2 * M - 1) (M + N - 1) : ℕ) : ℚ) := by
      rw [wzB_of_nonneg _ _ (by omega)]
      have htn : ((M : ℤ) - ((-(N : ℤ)) + 1)).toNat = M + N - 1 := by omega
      rw [htn]
    have h2 : wzB (2 * N - 1) ((N : ℤ) - ((-(N : ℤ)) + 1)) = 1 := by
      have hidx : (N : ℤ) - ((-(N : ℤ)) + 1) = ((2 * N - 1 : ℕ) : ℤ) := by omega
      rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast, Nat.choose_self,
        Nat.cast_one]
    have z1 : wzB (2 * N - 1) ((N : ℤ) - (-(N : ℤ))) = 0 := by
      exact wzB_gt _ _ (by omega)
    have hsign4 : (-1 : ℚ) ^ (((-(N : ℤ)) + 1) + 1) = (-1 : ℚ) ^ (-(N : ℤ)) := by
      rw [zpow_add_one₀ (by norm_num), zpow_add_one₀ (by norm_num)]
      ring
    unfold wzE wzElow wzG
    rw [e1, e2, l1, h1, h2, z1, hsign4]
    simp only [mul_one, mul_zero, sub_zero]
    linear_combination (-1 : ℚ) ^ (-(N : ℤ)) * wz_edge4_key M N hM hNM

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_flow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_flow_eq (M N : ℕ) (hM : 1 ≤ M) :
  wzF (M - 1) N
    = ∑ k ∈ Finset.Icc (max (-((M : ℤ) - 1)) (-(N : ℤ)))
      (min (((M : ℤ) - 1)) ((N : ℤ))), wzElow M N k := by
  have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
  have h2M : 2 * (M - 1) = 2 * M - 2 := by omega
  have term_eq : ∀ k : ℤ, wzE (M - 1) N k = wzElow M N k := by
    intro k
    simp only [wzE, wzElow, h2M, hcast]
  have rlo : max (-((M - 1 : ℕ) : ℤ)) (-(N : ℤ))
    = max (-((M : ℤ) - 1)) (-(N : ℤ)) := by rw [hcast]
  have rhi : min (((M - 1 : ℕ) : ℤ)) ((N : ℤ))
    = min (((M : ℤ) - 1)) ((N : ℤ)) := by rw [hcast]
  unfold wzF
  rw [rlo, rhi]
  exact Finset.sum_congr rfl (fun k _ => term_eq k)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_extend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_extend (M N : ℕ) (hM : 1 ≤ M) :
  (∑ k ∈ Finset.Icc (max (-((M : ℤ) - 1)) (-(N : ℤ)))
    (min (((M : ℤ) - 1)) ((N : ℤ))), wzElow M N k)
  = ∑ k ∈ Finset.Icc (max (-(M : ℤ)) (-(N : ℤ)))
    (min ((M : ℤ)) ((N : ℤ))), wzElow M N k := by
  by_cases hMN : M ≤ N
  · -- M ≤ N: S' = Icc(-(M-1), M-1), S = Icc(-M, M); add two vanishing points.
    have hlo : max (-((M : ℤ) - 1)) (-(N : ℤ)) = -((M : ℤ) - 1) := by
      apply max_eq_left
      omega
    have hhi : min (((M : ℤ) - 1)) ((N : ℤ)) = ((M : ℤ) - 1) := by
      apply min_eq_left
      omega
    have hSlo : max (-(M : ℤ)) (-(N : ℤ)) = -(M : ℤ) := by
      apply max_eq_left
      omega
    have hShi : min ((M : ℤ)) ((N : ℤ)) = (M : ℤ) := by
      apply min_eq_left
      omega
    rw [hlo, hhi, hSlo, hShi]
    have low0 : wzElow M N (-(M : ℤ)) = 0 := by
      unfold wzElow
      rw [show wzB (2 * M - 2) (((M : ℤ) - 1) + (-(M : ℤ))) = 0 from
        wzB_neg _ _ (by omega)]
      simp
    have high0 : wzElow M N ((M : ℤ)) = 0 := by
      unfold wzElow
      rw [show wzB (2 * M - 2) (((M : ℤ) - 1) + (M : ℤ)) = 0 from
        wzB_gt _ _ (by omega)]
      simp
    have hSS : Finset.Icc (-(M : ℤ)) ((M : ℤ))
      = insert (-(M : ℤ)) (insert ((M : ℤ))
        (Finset.Icc (-((M : ℤ) - 1)) (((M : ℤ) - 1)))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hmem1 : -(M : ℤ)
      ∉ insert ((M : ℤ)) (Finset.Icc (-((M : ℤ) - 1)) (((M : ℤ) - 1))) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hmem2 : (M : ℤ) ∉ Finset.Icc (-((M : ℤ) - 1)) (((M : ℤ) - 1)) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hSS, Finset.sum_insert hmem1, Finset.sum_insert hmem2, low0, high0]
    simp
  · have hNM : N < M := by omega
    -- N < M: the ranges coincide.
    have hlo : max (-((M : ℤ) - 1)) (-(N : ℤ)) = max (-(M : ℤ)) (-(N : ℤ)) := by
      have e1 : max (-((M : ℤ) - 1)) (-(N : ℤ)) = -(N : ℤ) := by
        apply max_eq_right
        omega
      have e2 : max (-(M : ℤ)) (-(N : ℤ)) = -(N : ℤ) := by
        apply max_eq_right
        omega
      rw [e1, e2]
    have hhi : min (((M : ℤ) - 1)) ((N : ℤ)) = min ((M : ℤ)) ((N : ℤ)) := by
      have e1 : min (((M : ℤ) - 1)) ((N : ℤ)) = (N : ℤ) := by
        apply min_eq_right
        omega
      have e2 : min ((M : ℤ)) ((N : ℤ)) = (N : ℤ) := by
        apply min_eq_right
        omega
      rw [e1, e2]
    rw [hlo, hhi]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_pointwise (M N : ℕ) (hM : 1 ≤ M) (k : ℤ)
  (hlo : max (-(M : ℤ)) (-(N : ℤ)) ≤ k)
  (hhi : k ≤ min ((M : ℤ)) ((N : ℤ))) :
  ((M : ℚ) + (N : ℚ)) * wzE M N k
    - 2 * (2 * (M : ℚ) - 1) * wzElow M N k
    = wzG M N (k + 1) - wzG M N k := by
  by_cases hMN : M ≤ N
  · have hbot : max (-(M : ℤ)) (-(N : ℤ)) = -(M : ℤ) := by
    apply max_eq_left
    omega
    have htop : min ((M : ℤ)) ((N : ℤ)) = (M : ℤ) := by
      apply min_eq_left
      omega
    by_cases hkbot : k = max (-(M : ℤ)) (-(N : ℤ))
    · subst hkbot
      rw [hbot]
      exact wz_edge3 M N hM hMN
    · by_cases hktop : k = min ((M : ℤ)) ((N : ℤ))
      · subst hktop
        rw [htop]
        exact wz_edge1 M N hM hMN
      · have hk1 : max (-(M : ℤ)) (-(N : ℤ)) + 1 ≤ k := by omega
        have hk2 : k ≤ min ((M : ℤ)) ((N : ℤ)) - 1 := by omega
        have hN : 1 ≤ N := by omega
        have c1 : wzB (2 * M) ((M : ℤ) + k)
          = ((Nat.choose (2 * M) (((M : ℤ) + k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have c2 : wzB (2 * N) ((N : ℤ) + k)
          = ((Nat.choose (2 * N) (((N : ℤ) + k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have c3 : wzB (2 * M - 2) (((M : ℤ) - 1) + k)
          = ((Nat.choose (2 * M - 2) ((((M : ℤ) - 1) + k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have e4 : (M : ℤ) - (k + 1) = (M : ℤ) - k - 1 := by ring
        have c4 : wzB (2 * M - 1) ((M : ℤ) - (k + 1))
          = ((Nat.choose (2 * M - 1) (((M : ℤ) - k - 1).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega), e4]
        have e5 : (N : ℤ) - (k + 1) = (N : ℤ) - k - 1 := by ring
        have c5 : wzB (2 * N - 1) ((N : ℤ) - (k + 1))
          = ((Nat.choose (2 * N - 1) (((N : ℤ) - k - 1).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega), e5]
        have c6 : wzB (2 * M - 1) ((M : ℤ) - k)
          = ((Nat.choose (2 * M - 1) (((M : ℤ) - k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have c7 : wzB (2 * N - 1) ((N : ℤ) - k)
          = ((Nat.choose (2 * N - 1) (((N : ℤ) - k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        unfold wzE wzElow wzG
        rw [c1, c2, c3, c4, c5, c6, c7]
        exact wz_interior M N hM hN k hk1 hk2
  · have hNM : N < M := by omega
    have hbot : max (-(M : ℤ)) (-(N : ℤ)) = -(N : ℤ) := by
      apply max_eq_right
      omega
    have htop : min ((M : ℤ)) ((N : ℤ)) = (N : ℤ) := by
      apply min_eq_right
      omega
    by_cases hkbot : k = max (-(M : ℤ)) (-(N : ℤ))
    · subst hkbot
      rw [hbot]
      exact wz_edge4 M N hM hNM
    · by_cases hktop : k = min ((M : ℤ)) ((N : ℤ))
      · subst hktop
        rw [htop]
        exact wz_edge2 M N hM hNM
      · have hk1 : max (-(M : ℤ)) (-(N : ℤ)) + 1 ≤ k := by omega
        have hk2 : k ≤ min ((M : ℤ)) ((N : ℤ)) - 1 := by omega
        have hN : 1 ≤ N := by omega
        have c1 : wzB (2 * M) ((M : ℤ) + k)
          = ((Nat.choose (2 * M) (((M : ℤ) + k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have c2 : wzB (2 * N) ((N : ℤ) + k)
          = ((Nat.choose (2 * N) (((N : ℤ) + k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have c3 : wzB (2 * M - 2) (((M : ℤ) - 1) + k)
          = ((Nat.choose (2 * M - 2) ((((M : ℤ) - 1) + k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have e4 : (M : ℤ) - (k + 1) = (M : ℤ) - k - 1 := by ring
        have c4 : wzB (2 * M - 1) ((M : ℤ) - (k + 1))
          = ((Nat.choose (2 * M - 1) (((M : ℤ) - k - 1).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega), e4]
        have e5 : (N : ℤ) - (k + 1) = (N : ℤ) - k - 1 := by ring
        have c5 : wzB (2 * N - 1) ((N : ℤ) - (k + 1))
          = ((Nat.choose (2 * N - 1) (((N : ℤ) - k - 1).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega), e5]
        have c6 : wzB (2 * M - 1) ((M : ℤ) - k)
          = ((Nat.choose (2 * M - 1) (((M : ℤ) - k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        have c7 : wzB (2 * N - 1) ((N : ℤ) - k)
          = ((Nat.choose (2 * N - 1) (((N : ℤ) - k).toNat) : ℕ) : ℚ) := by
          rw [wzB_of_nonneg _ _ (by omega)]
        unfold wzE wzElow wzG
        rw [c1, c2, c3, c4, c5, c6, c7]
        exact wz_interior M N hM hN k hk1 hk2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_recurrence (M N : ℕ) (hM : 1 ≤ M) :
  ((M : ℚ) + (N : ℚ)) * wzF M N - 2 * (2 * (M : ℚ) - 1) * wzF (M - 1) N = 0 := by
  rw [wz_flow_eq M N hM, wz_extend M N hM]
  have hab : max (-(M : ℤ)) (-(N : ℤ)) ≤ min ((M : ℤ)) ((N : ℤ)) + 1 := by
    omega
  have hpt : ∀ k ∈ Finset.Icc (max (-(M : ℤ)) (-(N : ℤ)))
    (min ((M : ℤ)) ((N : ℤ))),
    ((M : ℚ) + (N : ℚ)) * wzE M N k - 2 * (2 * (M : ℚ) - 1) * wzElow M N k
    = wzG M N (k + 1) - wzG M N k := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact wz_pointwise M N hM k hk.1 hk.2
  have hGtop : wzG M N (min ((M : ℤ)) ((N : ℤ)) + 1) = 0 := by
    by_cases hMN : M ≤ N
    · have e : min ((M : ℤ)) ((N : ℤ)) = (M : ℤ) := by
      apply min_eq_left
      omega
      rw [e]
      unfold wzG
      rw [show wzB (2 * M - 1) ((M : ℤ) - ((M : ℤ) + 1)) = 0 from
        wzB_neg _ _ (by omega)]
      simp
    · have e : min ((M : ℤ)) ((N : ℤ)) = (N : ℤ) := by
      apply min_eq_right
      omega
      rw [e]
      unfold wzG
      rw [show wzB (2 * N - 1) ((N : ℤ) - ((N : ℤ) + 1)) = 0 from
        wzB_neg _ _ (by omega)]
      simp
  have hGbot : wzG M N (max (-(M : ℤ)) (-(N : ℤ))) = 0 := by
    by_cases hMN : M ≤ N
    · have e : max (-(M : ℤ)) (-(N : ℤ)) = -(M : ℤ) := by
      apply max_eq_left
      omega
      rw [e]
      unfold wzG
      rw [show wzB (2 * M - 1) ((M : ℤ) - (-(M : ℤ))) = 0 from
        wzB_gt _ _ (by omega)]
      simp
    · by_cases hN0 : N = 0
      · subst hN0
        unfold wzG
        simp
      · have hN : 1 ≤ N := by omega
        have e : max (-(M : ℤ)) (-(N : ℤ)) = -(N : ℤ) := by
          apply max_eq_right
          omega
        rw [e]
        unfold wzG
        rw [show wzB (2 * N - 1) ((N : ℤ) - (-(N : ℤ))) = 0 from
          wzB_gt _ _ (by omega)]
        simp
  simp only [wzF]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl hpt, wz_sum_Icc_sub _ _ _ hab, hGtop, hGbot, sub_self]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_sign (k : ℤ) : (((-1 : ℤ) ^ k.natAbs : ℤ) : ℚ) = (-1 : ℚ) ^ k := by
  obtain he | ho := Int.even_or_odd k
  · have heN : Even k.natAbs := he.natAbs
    rw [heN.neg_one_pow, he.neg_one_zpow]
    simp
  · have hoN : Odd k.natAbs := ho.natAbs
    rw [hoN.neg_one_pow, ho.neg_one_zpow]
    simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_bridge (m n : ℕ) : wzF m n
  = (((∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min ((m : ℤ)) ((n : ℤ))),
    (-1 : ℤ) ^ k.natAbs * (Nat.choose (2 * m) (Int.toNat ((m : ℤ) + k)) : ℤ) *
      (Nat.choose (2 * n) (Int.toNat ((n : ℤ) + k)) : ℤ)) : ℤ) : ℚ) := by
  unfold wzF
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  unfold wzE
  rw [wzB_of_nonneg _ _ (by omega), wzB_of_nonneg _ _ (by omega)]
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [wz_sign k]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_base](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_base (N : ℕ) :
  wzF 0 N * (((Nat.factorial 0 : ℕ) : ℚ) * ((Nat.factorial N : ℕ) : ℚ) *
    ((Nat.factorial (0 + N) : ℕ) : ℚ))
  = ((Nat.factorial (2 * 0) : ℕ) : ℚ) * ((Nat.factorial (2 * N) : ℕ) : ℚ) := by
  have hF0 : wzF 0 N = ((Nat.choose (2 * N) N : ℕ) : ℚ) := by
    have hlo : max (-((0 : ℕ) : ℤ)) (-(N : ℤ)) = 0 := by omega
    have hhi : min (((0 : ℕ) : ℤ)) ((N : ℤ)) = 0 := by omega
    unfold wzF
    rw [hlo, hhi, Finset.Icc_self, Finset.sum_singleton]
    have b1 : wzB (2 * 0) (((0 : ℕ) : ℤ) + (0 : ℤ))
      = ((Nat.choose (2 * 0) 0 : ℕ) : ℚ) := by
      rw [wzB_of_nonneg _ _ (by omega)]
      have htn : (((0 : ℕ) : ℤ) + (0 : ℤ)).toNat = 0 := by omega
      rw [htn]
    have b2 : wzB (2 * N) (((N : ℕ) : ℤ) + (0 : ℤ))
      = ((Nat.choose (2 * N) N : ℕ) : ℚ) := by
      have hidx : ((N : ℕ) : ℤ) + (0 : ℤ) = ((N : ℕ) : ℤ) := by simp
      rw [hidx, wzB_of_nonneg _ _ (by positivity), Int.toNat_natCast]
    unfold wzE
    rw [b1, b2]
    simp
  have hC : (Nat.choose (2 * N) N) * (Nat.factorial N) * (Nat.factorial N)
    = Nat.factorial (2 * N) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show N ≤ 2 * N by omega)
    have e : 2 * N - N = N := by omega
    rwa [e] at h
  have hCq : ((Nat.choose (2 * N) N : ℕ) : ℚ)
    * (((Nat.factorial N : ℕ) : ℚ) * ((Nat.factorial N : ℕ) : ℚ))
    = ((Nat.factorial (2 * N) : ℕ) : ℚ) := by
    rw [← mul_assoc]
    exact_mod_cast hC
  simp only [Nat.factorial_zero, Nat.zero_add, mul_zero, Nat.cast_one, one_mul]
  rw [hF0]
  linear_combination hCq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wz_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
private lemma wz_key (m n : ℕ) :
  wzF m n * (((Nat.factorial m : ℕ) : ℚ) * ((Nat.factorial n : ℕ) : ℚ) *
    ((Nat.factorial (m + n) : ℕ) : ℚ))
  = ((Nat.factorial (2 * m) : ℕ) : ℚ) * ((Nat.factorial (2 * n) : ℕ) : ℚ) := by
  induction m with
  | zero => exact wz_base n
  | succ m ih =>
    have hM : 1 ≤ m + 1 := by omega
    have hrec := wz_recurrence (m + 1) n hM
    rw [Nat.add_sub_cancel] at hrec
    have r1 : ((Nat.factorial (m + 1) : ℕ) : ℚ)
      = ((m + 1 : ℕ) : ℚ) * ((Nat.factorial m : ℕ) : ℚ) := by
      have h : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m :=
        Nat.factorial_succ m
      rw [h, Nat.cast_mul]
    have r2 : ((Nat.factorial ((m + 1) + n) : ℕ) : ℚ)
      = (((m + 1 : ℕ) : ℚ) + ((n : ℕ) : ℚ)) * ((Nat.factorial (m + n) : ℕ) : ℚ) := by
      have h : (m + 1) + n = (m + n) + 1 := by omega
      have hf : Nat.factorial ((m + 1) + n) = ((m + 1) + n) * Nat.factorial (m + n) := by
        conv_lhs => rw [h]
        rw [Nat.factorial_succ, ← h]
      rw [hf, Nat.cast_mul]
      have hc : ((((m + 1) + n : ℕ)) : ℚ) = ((m + 1 : ℕ) : ℚ) + ((n : ℕ) : ℚ) := by
        push_cast
        ring
      rw [hc]
    have f1 : Nat.factorial (2 * (m + 1)) = (2 * (m + 1)) * Nat.factorial (2 * (m + 1) - 1) := by
      have e : 2 * (m + 1) = (2 * (m + 1) - 1) + 1 := by omega
      rw [e, Nat.factorial_succ, ← e]
    have f2 : Nat.factorial (2 * (m + 1) - 1)
      = (2 * (m + 1) - 1) * Nat.factorial (2 * m) := by
      have e : 2 * (m + 1) - 1 = (2 * m) + 1 := by omega
      rw [e, Nat.factorial_succ]
    have r3 : ((Nat.factorial (2 * (m + 1)) : ℕ) : ℚ)
      = (2 * ((m + 1 : ℕ) : ℚ)) * ((2 * ((m + 1 : ℕ) : ℚ)) - 1) *
        ((Nat.factorial (2 * m) : ℕ) : ℚ) := by
      rw [f1, f2]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      have c2 : (((2 * (m + 1) - 1 : ℕ)) : ℚ) = 2 * ((m + 1 : ℕ) : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * (m + 1))]
        push_cast
        ring
      rw [c2]
      ring
    rw [r1, r2, r3]
    linear_combination (((m + 1 : ℕ) : ℚ) *
      (((Nat.factorial m : ℕ) : ℚ) * ((Nat.factorial n : ℕ) : ℚ) *
        ((Nat.factorial (m + n) : ℕ) : ℚ))) * hrec +
      (((m + 1 : ℕ) : ℚ) * (2 * (2 * ((m + 1 : ℕ) : ℚ) - 1))) * ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[von_szily_super_catalan_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean)
-/
@[path]
lemma von_szily_super_catalan_identity
  {m n : ℕ} :
-- imply
  (((2 * m).factorial * (2 * n).factorial /
    (m.factorial * n.factorial * (m + n).factorial) : ℕ) : ℤ) =
    ∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min (m : ℤ) (n : ℤ)),
    (-1 : ℤ) ^ k.natAbs *
    (Nat.choose (2 * m) (Int.toNat ((m : ℤ) + k)) : ℤ) *
    (Nat.choose (2 * n) (Int.toNat ((n : ℤ) + k)) : ℤ) := by
-- proof
  have key := wz_key m n
  have br := wz_bridge m n
  have hq : ((((∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min ((m : ℤ)) ((n : ℤ))),
    (-1 : ℤ) ^ k.natAbs * (Nat.choose (2 * m) (Int.toNat ((m : ℤ) + k)) : ℤ) *
      (Nat.choose (2 * n) (Int.toNat ((n : ℤ) + k)) : ℤ)) : ℤ)) : ℚ) *
    (((Nat.factorial m : ℕ) : ℚ) * ((Nat.factorial n : ℕ) : ℚ) *
      ((Nat.factorial (m + n) : ℕ) : ℚ))
    = ((Nat.factorial (2 * m) : ℕ) : ℚ) * ((Nat.factorial (2 * n) : ℕ) : ℚ) := by
    rwa [← br]
  have hz : (∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min ((m : ℤ)) ((n : ℤ))),
    (-1 : ℤ) ^ k.natAbs * (Nat.choose (2 * m) (Int.toNat ((m : ℤ) + k)) : ℤ) *
      (Nat.choose (2 * n) (Int.toNat ((n : ℤ) + k)) : ℤ)) *
    (((m.factorial : ℕ) : ℤ) * ((n.factorial : ℕ) : ℤ) *
      (((m + n).factorial : ℕ) : ℤ))
    = (((2 * m).factorial : ℕ) : ℤ) * (((2 * n).factorial : ℕ) : ℤ) := by
    exact_mod_cast hq
  have hdvd : (Nat.factorial m * Nat.factorial n * Nat.factorial (m + n)) ∣
    (Nat.factorial (2 * m) * Nat.factorial (2 * n)) := by
    have hz' : (((Nat.factorial (2 * m) * Nat.factorial (2 * n) : ℕ)) : ℤ)
      = (((Nat.factorial m * Nat.factorial n * Nat.factorial (m + n) : ℕ)) : ℤ) *
        (∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min ((m : ℤ)) ((n : ℤ))),
        (-1 : ℤ) ^ k.natAbs * (Nat.choose (2 * m) (Int.toNat ((m : ℤ) + k)) : ℤ) *
          (Nat.choose (2 * n) (Int.toNat ((n : ℤ) + k)) : ℤ)) := by
      simp only [Nat.cast_mul]
      linear_combination -hz
    exact Int.natCast_dvd_natCast.mp ⟨_, hz'⟩
  have hdiv : ((((2 * m).factorial * (2 * n).factorial /
    (m.factorial * n.factorial * (m + n).factorial) : ℕ) : ℤ) : ℚ) =
    ((∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min ((m : ℤ)) ((n : ℤ))),
      (-1 : ℤ) ^ k.natAbs * (Nat.choose (2 * m) (Int.toNat ((m : ℤ) + k)) : ℤ) *
        (Nat.choose (2 * n) (Int.toNat ((n : ℤ) + k)) : ℤ) : ℤ) : ℚ) := by
    have hpos0 : ((((Nat.factorial m * Nat.factorial n * Nat.factorial (m + n) : ℕ)) : ℚ)) ≠ 0 := by
      simp only [Nat.cast_mul]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + n))
    rw [Int.cast_natCast, Nat.cast_div hdvd hpos0]
    simp only [Nat.cast_mul]
    have hpos : (((Nat.factorial m : ℕ)) : ℚ) * (((Nat.factorial n : ℕ)) : ℚ) *
      (((Nat.factorial (m + n) : ℕ)) : ℚ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + n))
    rw [div_eq_iff hpos]
    linear_combination -hq
  exact_mod_cast hdiv

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
