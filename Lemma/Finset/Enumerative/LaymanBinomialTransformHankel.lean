import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.LaymanBinomialTransformHankel
open MetaMathlibExt


namespace MetaMathlibExt

/--
[laymanBinomMatrix_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean)
-/
@[path]
private lemma laymanBinomMatrix_lower (n : ℕ) :
  (laymanBinomMatrix n).IsLowerTriangular := by
  intro i j h
  simp only [laymanBinomMatrix, Matrix.of_apply]
  have hij : i < j := by simpa using h
  have hval : i.val < j.val := by exact_mod_cast hij
  rw [Nat.choose_eq_zero_of_lt hval, Nat.cast_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[laymanBinomMatrix_diag](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean)
-/
@[path]
private lemma laymanBinomMatrix_diag (n : ℕ) (i : Fin (n + 1)) :
  laymanBinomMatrix n i i = 1 := by
  simp [laymanBinomMatrix, Nat.choose_self]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[laymanBinomMatrix_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean)
-/
@[path]
private lemma laymanBinomMatrix_det (n : ℕ) : (laymanBinomMatrix n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (laymanBinomMatrix_lower n)]
  simp [laymanBinomMatrix_diag]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[layman_entry_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean)
-/
@[path]
transform sum. -/
private lemma layman_entry_sum (a : ℕ → ℤ) (u v : ℕ) :
  ∑ l ∈ Finset.range (u + 1), ∑ m ∈ Finset.range (v + 1),
    ((Nat.choose u l : ℤ) * (Nat.choose v m : ℤ) * a (l + m))
    = ∑ k ∈ Finset.range (u + v + 1), (Nat.choose (u + v) k : ℤ) * a k := by
  classical
  let e : ℕ × ℕ → Sigma (fun _ : ℕ => ℕ × ℕ) := fun p => ⟨p.1 + p.2, p⟩
  let G : Sigma (fun _ : ℕ => ℕ × ℕ) → ℤ :=
    fun x => (Nat.choose u x.2.1 : ℤ) * (Nat.choose v x.2.2 : ℤ) * a (x.2.1 + x.2.2)
  let S : Finset (ℕ × ℕ) := Finset.range (u + 1) ×ˢ Finset.range (v + 1)
  let T : Finset (Sigma fun _ : ℕ => ℕ × ℕ) :=
    Finset.sigma (Finset.range (u + v + 1)) fun k =>
      Finset.HasAntidiagonal.antidiagonal k
  have he_inj : Set.InjOn e S := by
    intro x1 _ x2 _ h
    have h2 : x1 = x2 := congrArg Sigma.snd h
    simpa [e] using h2
  have hLHS : ∑ x ∈ S.image e, G x
    = ∑ l ∈ Finset.range (u + 1), ∑ m ∈ Finset.range (v + 1),
      ((Nat.choose u l : ℤ) * (Nat.choose v m : ℤ) * a (l + m)) := by
    rw [Finset.sum_image he_inj]
    simp only [S, Finset.sum_product]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    simp [G, e]
  have hsub : S.image e ⊆ T := by
    intro x hx
    simp only [S, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨l, m⟩, ⟨hl, hm⟩, rfl⟩ := hx
    change (⟨l + m, (l, m)⟩ : Sigma fun _ : ℕ => ℕ × ℕ) ∈ T
    simp only [T, Finset.mem_sigma, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  have hT : ∑ x ∈ T, G x = ∑ x ∈ S.image e, G x := by
    apply Eq.symm
    apply Finset.sum_subset hsub
    intro x hxT hx0
    obtain ⟨k, p⟩ := x
    obtain ⟨l, m⟩ := p
    have hsig : k ∈ Finset.range (u + v + 1) ∧
      (l, m) ∈ Finset.HasAntidiagonal.antidiagonal k :=
      Finset.mem_sigma.mp hxT
    have hkk : l + m = k :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hsig.2
    have hmemS : (l, m) ∉ S := by
      intro hS
      apply hx0
      rw [Finset.mem_image]
      refine ⟨(l, m), hS, ?_⟩
      simp only [e]
      rw [hkk]
    change (Nat.choose u l : ℤ) * (Nat.choose v m : ℤ) * a (l + m) = 0
    simp only [S, Finset.mem_product, Finset.mem_range, not_and_or] at hmemS
    obtain h | h := hmemS
    · have hu : u < l := by omega
      rw [Nat.choose_eq_zero_of_lt hu, Nat.cast_zero, zero_mul, zero_mul]
    · have hv : v < m := by omega
      rw [Nat.choose_eq_zero_of_lt hv, Nat.cast_zero, mul_zero, zero_mul]
  have hTsum : ∑ x ∈ T, G x
    = ∑ k ∈ Finset.range (u + v + 1),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        ((Nat.choose u p.1 : ℤ) * (Nat.choose v p.2 : ℤ) * a (p.1 + p.2)) := by
    simp [T, G, Finset.sum_sigma]
  have hV : ∀ k ∈ Finset.range (u + v + 1),
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      ((Nat.choose u p.1 : ℤ) * (Nat.choose v p.2 : ℤ) * a (p.1 + p.2))
      = (Nat.choose (u + v) k : ℤ) * a k := by
    intro k hk
    have hsub2 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      (Nat.choose u p.1 : ℤ) * (Nat.choose v p.2 : ℤ) * a (p.1 + p.2)
        = ((Nat.choose u p.1 * Nat.choose v p.2 : ℕ) : ℤ) * a k := by
      intro p hp
      have hkk : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [hkk, Nat.cast_mul]
    rw [Finset.sum_congr rfl hsub2, ← Finset.sum_mul]
    congr 1
    have hnat : (u + v).choose k
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, u.choose ij.1 * v.choose ij.2 :=
      Nat.add_choose_eq u v k
    rw [hnat, Nat.cast_sum]
  rw [← hLHS, ← hT, hTsum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact hV k hk

end MetaMathlibExt

namespace MetaMathlibExt

/--
[layman_hankel_entry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean)
-/
@[path]
private lemma layman_hankel_entry (a : ℕ → ℤ) (n : ℕ) (p q : Fin (n + 1)) :
  (laymanBinomMatrix n *
    (Matrix.of fun i j : Fin (n + 1) ↦ a (i.val + j.val)) *
    (laymanBinomMatrix n).transpose) p q
    = binomialTransform a (p.val + q.val) := by
  have hpn : p.val ≤ n := by have h := p.isLt; omega
  have hqn : q.val ≤ n := by have h := q.isLt; omega
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    laymanBinomMatrix]
  have hinner : ∀ x : Fin (n + 1),
    (∑ l : Fin (n + 1), (Nat.choose p.val l.val : ℤ) * a (l.val + x.val))
    = ∑ l ∈ Finset.range (p.val + 1),
      (Nat.choose p.val l : ℤ) * a (l + x.val) := by
    intro x
    rw [Fin.sum_univ_eq_sum_range
      (fun m => (Nat.choose p.val m : ℤ) * a (m + x.val)) (n + 1)]
    apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro l hl1 hl2
    simp only [Finset.mem_range] at hl1 hl2
    have hpl : p.val < l := by omega
    rw [Nat.choose_eq_zero_of_lt hpl, Nat.cast_zero, zero_mul]
  simp only [hinner]
  have houter : (∑ x : Fin (n + 1),
    (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + x.val)) *
    (Nat.choose q.val x.val : ℤ))
    = ∑ x ∈ Finset.range (q.val + 1),
      (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + x)) *
      (Nat.choose q.val x : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun m =>
      (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + m)) *
        (Nat.choose q.val m : ℤ)) (n + 1)]
    apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro x hx1 hx2
    simp only [Finset.mem_range] at hx1 hx2
    have hqx : q.val < x := by omega
    rw [Nat.choose_eq_zero_of_lt hqx, Nat.cast_zero, mul_zero]
  rw [houter, binomialTransform_eq_sum]
  have hform : (∑ x ∈ Finset.range (q.val + 1),
    (∑ l ∈ Finset.range (p.val + 1), (Nat.choose p.val l : ℤ) * a (l + x)) *
    (Nat.choose q.val x : ℤ))
    = ∑ l ∈ Finset.range (p.val + 1), ∑ m ∈ Finset.range (q.val + 1),
      (Nat.choose p.val l : ℤ) * (Nat.choose q.val m : ℤ) * a (l + m) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hform]
  exact layman_entry_sum a p.val q.val

end MetaMathlibExt

namespace MetaMathlibExt

/--
[layman_binomial_transform_hankel_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanBinomialTransformHankel.lean)
-/
@[path]
lemma layman_binomial_transform_hankel_invariant
  {a : ℕ → ℤ} :
-- imply
  hankelTransform (binomialTransform a) = hankelTransform a := by
-- proof
  funext n
  simp only [hankelTransform]
  have hmat : (Matrix.of fun i j : Fin (n + 1) ↦ binomialTransform a (i.val + j.val))
    = laymanBinomMatrix n *
      (Matrix.of fun i j : Fin (n + 1) ↦ a (i.val + j.val)) *
      (laymanBinomMatrix n).transpose := by
    ext i j
    simp only [Matrix.of_apply]
    exact (layman_hankel_entry a n i j).symm
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    laymanBinomMatrix_det, one_mul, mul_one]
end



-- created on 2026-10-20
-- updated on 2026-10-26
