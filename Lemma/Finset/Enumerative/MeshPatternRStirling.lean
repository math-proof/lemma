import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.MeshPatternRStirling.Part3
open MetaMathlibExt


namespace MetaMathlibExt

/--
[poly_C_eq_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma poly_C_eq_natCast (a : ℕ) :
  (Polynomial.C a : Polynomial ℕ) = ((a : ℕ) : Polynomial ℕ) :=
  Polynomial.C_eq_natCast a

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rStirlingFirst_add_eq_coeff_prod_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma rStirlingFirst_add_eq_coeff_prod_range (n r j : ℕ) :
  rStirlingFirst n (j + r) r =
    (∏ i ∈ Finset.range (n - r),
      ((Polynomial.X : Polynomial ℕ) + ((r + i : ℕ) : Polynomial ℕ))).coeff j := by
  unfold rStirlingFirst
  rw [Polynomial.coeff_X_pow_mul]
  have h : (∏ k ∈ Finset.Ico r n,
    ((Polynomial.X : Polynomial ℕ) + Polynomial.C k)) =
    (∏ i ∈ Finset.range (n - r),
      ((Polynomial.X : Polynomial ℕ) + ((r + i : ℕ) : Polynomial ℕ))) := by
    rw [Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i _
    simp
  rw [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[perm_fin_exists_globalMax](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma perm_fin_exists_globalMax {n : ℕ} (hn : 0 < n)
  (σ : Equiv.Perm (Fin n)) : ∃ M : Fin n, ∀ h, σ h ≤ σ M := by
  obtain ⟨m, hm⟩ : ∃ m : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
  obtain ⟨M, _, hM⟩ :=
    Finset.exists_max_image Finset.univ (fun i => σ i) ⟨m, Finset.mem_univ m⟩
  exact ⟨M, fun h => hM h (Finset.mem_univ h)⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[perm_fin_globalMax_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma perm_fin_globalMax_unique {n : ℕ} (σ : Equiv.Perm (Fin n))
  (a b : Fin n) (ha : ∀ h, σ h ≤ σ a) (hb : ∀ h, σ h ≤ σ b) : a = b := by
  have h1 : σ b ≤ σ a := ha b
  have h2 : σ a ≤ σ b := hb a
  have heq : σ a = σ b := le_antisymm h2 h1
  exact Equiv.injective σ heq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fintype_card_fiber_eq_coeff_sum_X_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma fintype_card_fiber_eq_coeff_sum_X_pow {α : Type*} [Fintype α]
  (f : α → ℕ) (j : ℕ) :
  Fintype.card {a // f a = j} =
    (∑ a, (Polynomial.X : Polynomial ℕ) ^ f a).coeff j := by
  classical
  rw [Polynomial.finsetSum_coeff Finset.univ]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  rw [Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro x _
  rw [eq_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meshPoly_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma meshPoly_step (k m : ℕ) (hk : 1 < k) (hm : k ≤ m) :
  PolyN m k =
    (Polynomial.X + (((m - 1 : ℕ)) : Polynomial ℕ)) * PolyN (m - 1) k := by
  have h : PolyN m k =
    (Polynomial.X + Polynomial.C (m - 1)) * PolyN (m - 1) k :=
    (meshPatternCount_stirlingRecursion k m 1 hk hm one_pos).2.1
  rwa [poly_C_eq_natCast] at h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meshPoly_base](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma meshPoly_base (k : ℕ) (hk : 1 < k) :
  PolyN (k - 1) k = ((((k - 1).factorial : ℕ)) : Polynomial ℕ) := by
  have h : PolyN (k - 1) k = Polynomial.C ((k - 1).factorial) :=
    (meshPatternCount_stirlingRecursion k k 1 hk le_rfl one_pos).2.2.2
  rwa [poly_C_eq_natCast] at h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meshPoly_eq_factorial_mul_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma meshPoly_eq_factorial_mul_prod (n k : ℕ) (hkn : k ≤ n) (hk : 2 ≤ k) :
  PolyN n k =
    ((((k - 1).factorial : ℕ)) : Polynomial ℕ) *
      ∏ i ∈ Finset.range (n - k + 1),
        (Polynomial.X + ((((k - 1 + i : ℕ))) : Polynomial ℕ)) := by
  have hk1 : 1 < k := by omega
  have hk0 : 0 < k := by omega
  exact meshPatternGeneratingFunction_eq_factorial_mul_prod_general PolyN n k
    Polynomial.X hk0 hkn (meshPoly_base k hk1)
    (fun m hm => meshPoly_step k m hk1 hm)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meshWantedCount_eq_meshN](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma meshWantedCount_eq_meshN {n k : ℕ} (hn : 0 < n)
  (σ : Equiv.Perm (Fin n)) :
  meshWantedCount k σ = meshN k σ := by
  obtain ⟨M, hM⟩ := perm_fin_exists_globalMax hn σ
  have hsub : ∀ q : Fin n,
    (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ↔ q < M := by
    intro q
    constructor
    · intro h
      exact h M hM
    · intro hqm m hm
      have hmM : m = M := perm_fin_globalMax_unique σ m M hm hM
      rwa [hmM]
  have hfil : ∀ i : Fin n,
    (Finset.univ.filter fun t : Fin n => i < t ∧ t < M ∧ σ i < σ t) =
      (Finset.univ.filter fun q : Fin n =>
        i < q ∧ (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ∧ σ i < σ q) := by
    intro i
    apply Finset.ext
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hiq, hqM, hlt⟩
      exact ⟨hiq, (hsub q).mpr hqM, hlt⟩
    · rintro ⟨hiq, hq, hlt⟩
      exact ⟨hiq, (hsub q).mp hq, hlt⟩
  have hpw : ∀ i : Fin n, meshWantedMatch k σ i ↔ MatchPred k σ i := by
    intro i
    unfold meshWantedMatch MatchPred
    constructor
    · rintro ⟨hltr, hcard⟩
      refine ⟨M, hM, ?_, hltr⟩
      rwa [hfil i]
    · rintro ⟨maxIndex, hmax, hcard, hltr⟩
      have hMM : maxIndex = M := perm_fin_globalMax_unique σ maxIndex M hmax hM
      subst hMM
      refine ⟨hltr, ?_⟩
      rwa [← hfil i]
  have houter : (Finset.univ.filter (meshWantedMatch k σ)) =
    (Finset.univ.filter (MatchPred k σ)) := by
    apply Finset.filter_congr
    intro i _
    exact hpw i
  -- The two zero predicates are the same proposition up to bound-variable
  -- names (and defeq decidability instances), so `congr` closes the goal.
  unfold meshWantedCount meshN
  rw [houter]
  congr 1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_X_pow_meshWantedCount_eq_PolyN](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
private lemma sum_X_pow_meshWantedCount_eq_PolyN {n k : ℕ} (hn : 0 < n) :
  (∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshWantedCount k σ) =
    PolyN n k := by
  show (∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshWantedCount k σ) =
    ∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshN k σ
  apply Finset.sum_congr rfl
  intro σ _
  rw [meshWantedCount_eq_meshN hn σ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meshPatternCount_eq_factorial_mul_rStirlingNumber_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
lemma meshPatternCount_eq_factorial_mul_rStirlingNumber_general
  {n k j : ℕ}
-- given
  (hkn : k ≤ n)
  (hk : 2 ≤ k) :
-- imply
  Fintype.card {σ : Equiv.Perm (Fin n) // meshN k σ = j} =
    (k - 1).factorial * rStirlingFirst n (j + k - 1) (k - 1) := by
-- proof
  have hsum : (∑ σ : Equiv.Perm (Fin n), (Polynomial.X : Polynomial ℕ) ^ meshN k σ) =
    PolyN n k := rfl
  rw [fintype_card_fiber_eq_coeff_sum_X_pow]
  rw [hsum]
  rw [meshPoly_eq_factorial_mul_prod n k hkn hk]
  rw [Polynomial.coeff_natCast_mul]
  simp only [Nat.cast_id]
  have hjk : j + k - 1 = j + (k - 1) := by omega
  rw [hjk]
  rw [rStirlingFirst_add_eq_coeff_prod_range n (k - 1) j]
  have hrange : n - (k - 1) = n - k + 1 := by omega
  rw [hrange]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meshPatternCount_eq_factorial_mul_rStirlingNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean)
-/
@[path]
lemma meshPatternCount_eq_factorial_mul_rStirlingNumber
  {n k j : ℕ}
-- given
  (hkn : k ≤ n)
  (hk : 2 ≤ k) :
-- imply
  let isLeftToRightMaximum := by
-- proof
  have hn : 0 < n := by omega
  change Fintype.card {σ : Equiv.Perm (Fin n) // meshWantedCount k σ = j} =
    (k - 1).factorial * rStirlingFirst n (j + k - 1) (k - 1)
  simp only [meshWantedCount_eq_meshN hn]
  exact meshPatternCount_eq_factorial_mul_rStirlingNumber_general n k j hkn hk
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-26
