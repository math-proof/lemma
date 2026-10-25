import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part3
open MetaMathlibExt


namespace MetaMathlibExt

/--
[maxUnique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma maxUnique (m : ℕ) (σ : Equiv.Perm (Fin m)) (a b : Fin m)
  (ha : ∀ t : Fin m, σ t ≤ σ a) (hb : ∀ t : Fin m, σ t ≤ σ b) : a = b := by
  have h1 : σ b ≤ σ a := ha b
  have h2 : σ a ≤ σ b := hb a
  have heq : σ a = σ b := le_antisymm h2 h1
  exact σ.injective heq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[maxExists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma maxExists (m : ℕ) (mpos : 0 < m) (σ : Equiv.Perm (Fin m)) :
  ∃ M : Fin m, ∀ t : Fin m, σ t ≤ σ M := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, mpos⟩⟩
  obtain ⟨M, _, hM⟩ := Finset.exists_max_image Finset.univ (fun t => σ t) hne
  exact ⟨M, fun t => hM t (Finset.mem_univ t)⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zero_of_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma zero_of_max (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m))
  (M : Fin m) (hM : ∀ t : Fin m, σ t ≤ σ M) :
  ZeroPred r σ ↔ r ≤ M.val + 1 := by
  constructor
  · rintro ⟨a, ha, hr⟩
    have e : a = M := maxUnique m σ a M ha hM
    subst e
    exact hr
  · intro hr
    exact ⟨M, hM, hr⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[match_of_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma match_of_max (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m))
  (M : Fin m) (hM : ∀ t : Fin m, σ t ≤ σ M) (i : Fin m) :
  MatchPred r σ i ↔
    ((∀ t : Fin m, t < i → σ t < σ i) ∧
      r - 1 ≤ (Finset.univ.filter fun t : Fin m => i < t ∧ t < M ∧ σ i < σ t).card) := by
  constructor
  · rintro ⟨a, ha, hc, hl⟩
    have e : a = M := maxUnique m σ a M ha hM
    subst e
    exact ⟨hl, hc⟩
  · rintro ⟨hl, hc⟩
    exact ⟨M, hM, hc, hl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[vanish_meshN](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma vanish_meshN (m k : ℕ) (σ : Equiv.Perm (Fin m))
  (M : Fin m) (hM : ∀ t : Fin m, σ t ≤ σ M) (hMb : M.val + 2 ≤ k) :
  meshN k σ = 0 := by
  have hZ : ¬ ZeroPred k σ := by
    rw [zero_of_max m k σ M hM]
    omega
  have hN : ∀ i : Fin m, ¬ MatchPred k σ i := by
    intro i hi
    rw [match_of_max m k σ M hM i] at hi
    obtain ⟨-, hc⟩ := hi
    have hsub : Finset.univ.filter
      (fun t : Fin m => i < t ∧ t < M ∧ σ i < σ t) ⊆ Finset.Iio M := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_Iio]
      exact hx.2.1
    have hle := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hle
    omega
  have hfilter : Finset.univ.filter (MatchPred k σ) = ∅ :=
    Finset.filter_false_of_mem (fun x _ => hN x)
  unfold meshN
  simp [hfilter, hZ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[base_poly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma base_poly (k : ℕ) (hk : 1 < k) :
  PolyN (k - 1) k = Polynomial.C (Nat.factorial (k - 1)) := by
  have mpos : 0 < k - 1 := by omega
  have hterm : ∀ σ : Equiv.Perm (Fin (k - 1)),
    (Polynomial.X : Polynomial ℕ) ^ meshN k σ = 1 := by
    intro σ
    obtain ⟨M, hM⟩ := maxExists (k - 1) mpos σ
    have hMb : M.val + 2 ≤ k := by
      have hlt := M.isLt
      omega
    rw [vanish_meshN (k - 1) k σ M hM hMb]
    exact pow_zero _
  change ∑ σ : Equiv.Perm (Fin (k - 1)), (Polynomial.X : Polynomial ℕ) ^ meshN k σ
    = Polynomial.C (Nat.factorial (k - 1))
  simp only [hterm]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin (k - 1)))).card
    = Nat.factorial (k - 1) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeff_rec_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma coeff_rec_succ (c j' : ℕ) (Q : Polynomial ℕ) :
  ((Polynomial.X + Polynomial.C c) * Q).coeff (j' + 1)
    = Q.coeff j' + c * Q.coeff (j' + 1) := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeff_rec_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma coeff_rec_zero (c : ℕ) (Q : Polynomial ℕ) :
  ((Polynomial.X + Polynomial.C c) * Q).coeff 0 = c * Q.coeff 0 := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul_zero,
    Polynomial.coeff_C_mul, zero_add]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[poly_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma poly_reindex (m k : ℕ) : PolyN (m.succ) k
  = ∑ _pr : Fin (m.succ) × Equiv.Perm (Fin m),
    (Polynomial.X : Polynomial ℕ) ^ meshN k (Phi m _pr.1 _pr.2) := by
  change (∑ σ : Equiv.Perm (Fin (m.succ)), (Polynomial.X : Polynomial ℕ) ^ meshN k σ) = _
  exact (Fintype.sum_equiv (PhiEquiv m)
    (fun _pr : Fin (m.succ) × Equiv.Perm (Fin m) =>
      (Polynomial.X : Polynomial ℕ) ^ meshN k (Phi m _pr.1 _pr.2))
    (fun σ : Equiv.Perm (Fin (m.succ)) => (Polynomial.X : Polynomial ℕ) ^ meshN k σ)
    (fun _pr => rfl)).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[succAbove_val_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma succAbove_val_add (m : ℕ) (p : Fin (m.succ)) (i : Fin m) :
  (p.succAbove i).val = i.val + (if p.val ≤ i.val then 1 else 0) := by
  by_cases h : p.val ≤ i.val
  · have hle : p ≤ i.castSucc := by
    rwa [Fin.le_iff_val_le_val, Fin.val_castSucc]
    rw [Fin.succAbove_of_le_castSucc p i hle, Fin.val_succ]
    simp [h]
  · have hlt : i.castSucc < p := by
    rw [Fin.castSucc_lt_iff_succ_le, Fin.le_iff_val_le_val, Fin.val_succ]
    omega
    rw [Fin.succAbove_of_castSucc_lt p i hlt, Fin.val_castSucc]
    simp [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[maxPos_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma maxPos_max (t : ℕ) (τ : Equiv.Perm (Fin (t.succ))) :
  ∀ x : Fin (t.succ), τ x ≤ τ (maxPos t τ) := by
  intro x
  change τ x ≤ τ (τ.symm (Fin.last t))
  rw [Equiv.apply_symm_apply]
  exact Fin.le_last _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fiber_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma fiber_card_eq (t u₁ u₂ : ℕ) (h₁ : u₁ < t.succ) (h₂ : u₂ < t.succ) :
  (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u₁)).card
    = (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u₂)).card := by
  obtain ⟨a, ha⟩ : ∃ a : Fin (t.succ), a.val = u₁ := ⟨⟨u₁, h₁⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (t.succ), b.val = u₂ := ⟨⟨u₂, h₂⟩, rfl⟩
  have hss : Equiv.swap a b * Equiv.swap a b = 1 := Equiv.swap_mul_self a b
  have hsM : ∀ τ : Equiv.Perm (Fin (t.succ)),
    Equiv.swap a b (Equiv.swap a b (maxPos t τ)) = maxPos t τ := fun τ => by
    have h := congrArg (· (maxPos t τ)) hss
    simp
  have hsym : ∀ τ : Equiv.Perm (Fin (t.succ)),
    (τ * Equiv.swap a b).symm (Fin.last t) = Equiv.swap a b (maxPos t τ) := by
    intro τ
    rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, hsM τ]
    exact (Equiv.apply_symm_apply τ (Fin.last t)).symm
  have hmap : ∀ τ : Equiv.Perm (Fin (t.succ)),
    (maxPos t (τ * Equiv.swap a b)).val
      = (Equiv.swap a b (maxPos t τ)).val := by
    intro τ
    change ((τ * Equiv.swap a b).symm (Fin.last t)).val = _
    rw [hsym]
  apply Finset.card_bij (fun τ _ => τ * Equiv.swap a b)
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    have hMa : maxPos t τ = a := Fin.ext (hτ.trans ha.symm)
    rwa [hmap, hMa, Equiv.swap_apply_left]
  · intro τ₁ _ τ₂ _ h
    exact mul_right_cancel h
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨σ * Equiv.swap a b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hMb : maxPos t σ = b := Fin.ext (hσ.trans hb.symm)
      rwa [hmap, hMb, Equiv.swap_apply_right]
    · show σ * Equiv.swap a b * Equiv.swap a b = σ
      rw [mul_assoc, hss, mul_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma fiber_card (t u : ℕ) (hu : u < t.succ) :
  (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u)).card
    = Nat.factorial t := by
  have htot : (Finset.univ : Finset (Equiv.Perm (Fin (t.succ)))).card
    = Nat.factorial (t + 1) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hmaps : Set.MapsTo (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val)
    ↑(Finset.univ : Finset (Equiv.Perm (Fin (t.succ)))) ↑(Finset.range (t + 1)) := by
    intro τ _
    simp only [Finset.mem_coe, Finset.mem_range]
    exact (maxPos t τ).isLt
  have hfib := Finset.card_eq_sum_card_fiberwise (f :=
    fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val)
    (s := Finset.univ) (t := Finset.range (t + 1)) hmaps
  have hconst : ∀ v ∈ Finset.range (t + 1),
    (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = v)).card
      = (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val =
        u)).card := by
    intro v hv
    exact fiber_card_eq t v u (Finset.mem_range.mp hv) hu
  rw [htot, Finset.sum_eq_card_nsmul hconst, Finset.card_range, smul_eq_mul,
    Nat.factorial_succ] at hfib
  exact (Nat.mul_left_cancel (Nat.succ_pos t) hfib).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[filter_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma filter_le_card (t a : ℕ) (h : a ≤ t) :
  (Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)).card = a + 1 := by
  have hF : Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)
    = Finset.Iio (⟨a + 1, by omega⟩ : Fin ((t.succ).succ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
      Fin.lt_def]
    show p.val ≤ a ↔ p.val < a + 1
    omega
  rw [hF, Fin.card_Iio]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[filter_card_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma filter_card_add (t a : ℕ) (h : a ≤ t) :
  (Finset.univ.filter (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card + (a + 1)
    = (t.succ).succ := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin ((t.succ).succ)))) (fun p => p.val ≤ a)
  rw [filter_le_card t a h] at hsum
  have hU : (Finset.univ : Finset (Fin ((t.succ).succ))).card = (t.succ).succ := by
    rw [Finset.card_univ, Fintype.card_fin]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[aggregate_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma aggregate_identity (a T K Fc : ℕ) (X Cm : Polynomial ℕ)
  (hC : ((T : ℕ) : Polynomial ℕ) = Cm)
  (hK : K + (a + 1) = T + 1) :
  a • (Fc • ((((T + 1 : ℕ))) • (1 : Polynomial ℕ)))
    + Fc • ((a + 1) • X + K • (1 : Polynomial ℕ))
    = ((a + 1) * Fc) • (X + Cm) := by
  have haK : a + K = T := by omega
  have hnat : a * (T + 1) + K = (a + 1) * T := by
    calc a * (T + 1) + K = a * T + (a + K) := by ring
      _ = a * T + T := by rw [haK]
      _ = (a + 1) * T := by ring
  have hnatC : ((a * (T + 1) + K : ℕ) : Polynomial ℕ) = (((a + 1) * T : ℕ)) := by
    exact_mod_cast hnat
  have e1 : ((a : Polynomial ℕ) * (((T + 1 : ℕ)) : Polynomial ℕ) + (K : Polynomial ℕ))
    = ((a + 1 : ℕ) : Polynomial ℕ) * (T : Polynomial ℕ) := by
    conv_lhs => rw [← Nat.cast_mul, ← Nat.cast_add, hnatC, Nat.cast_mul]
  simp only [nsmul_eq_mul, mul_one]
  rw [← hC, Nat.cast_mul]
  rw [show ((a : Polynomial ℕ) * ((Fc : Polynomial ℕ) * (((T + 1 : ℕ)) : Polynomial ℕ))
    + (Fc : Polynomial ℕ) * (((a + 1 : ℕ) : Polynomial ℕ) * X + (K : Polynomial ℕ)))
    = (Fc : Polynomial ℕ) * ((a : Polynomial ℕ) * (((T + 1 : ℕ)) : Polynomial ℕ)
      + (K : Polynomial ℕ))
      + (Fc : Polynomial ℕ) * (((a + 1 : ℕ) : Polynomial ℕ) * X) from by ring, e1]
  ring

end MetaMathlibExt

/--
[meshPatternCount_stirlingRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean)
-/
@[path]
private lemma meshPatternCount_stirlingRecursion_eq
  {k n j : ℕ}
-- given
  (hk : 1 < k)
  (hn : k ≤ n)
  (hj : 0 < j) :
-- imply
  let isMeshMatch : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → Fin m → Prop := by
-- proof
  apply MetaMathlibExt.meshPatternCount_stirlingRecursion k n j hk hn hj


-- created on 2026-10-20
-- updated on 2026-10-23
