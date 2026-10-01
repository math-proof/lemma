import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n u v : ℕ}
-- given
  (_hu : u < n + 1)
  (hv : v < n + 1) :
-- imply
  ∀ x ∈ {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = u}, ∀ X : Fin (n + 1) → ℕ, (fun i => (X i : ℂ)) = swapMatrix (Fin.last n) (Fin.ofNat (n + 1) (∑ k : Fin (n + 1), (if x k = v then 1 else 0) * (k : ℕ))) *ᵥ (fun i => (x i : ℂ)) → X ∈ {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = v} ∧ (fun i => (x i : ℂ)) = swapMatrix (Fin.last n) (Fin.ofNat (n + 1) (∑ k : Fin (n + 1), (if X k = u then 1 else 0) * (k : ℕ))) *ᵥ (fun i => (X i : ℂ)) := by
-- proof
  intro x ⟨himg, hlast⟩ X hX
  have hinj : Function.Injective x := by
    have hc := Finset.card_image_iff.mp (show (Finset.univ.image x).card = (Finset.univ : Finset (Fin (n + 1))).card by rw [himg]; simp)
    exact fun a b e => hc (by simp) (by simp) e
  have mulv : ∀ (i j : Fin (n + 1)) (y : Fin (n + 1) → ℂ), swapMatrix i j *ᵥ y = y ∘ Equiv.swap i j := by
    intro i j y
    funext a
    simp [swapMatrix, Matrix.mulVec, dotProduct]
  have idx : ∀ (y : Fin (n + 1) → ℕ) (c : ℕ) (q : Fin (n + 1)), Function.Injective y → y q = c →
      Fin.ofNat (n + 1) (∑ k : Fin (n + 1), (if y k = c then 1 else 0) * (k : ℕ)) = q := by
    intro y c q hy hq
    rw [Finset.sum_eq_single q]
    · apply Fin.ext
      simp [hq, Fin.ofNat, Nat.mod_eq_of_lt q.isLt]
    · intro b _ hb
      rw [if_neg (fun e => hb (hy (e.trans hq.symm)))]
      simp
    · simp
  obtain ⟨p, hp⟩ : ∃ p, x p = v := by
    have : v ∈ Finset.univ.image x := by rw [himg]; simpa using hv
    simpa using this
  rw [idx x v p hinj hp, mulv] at hX
  have hXeq : X = x ∘ Equiv.swap (Fin.last n) p := by
    funext i
    have := congrFun hX i
    simp only [Function.comp] at this
    exact_mod_cast this
  subst hXeq
  have hinjX : Function.Injective (x ∘ Equiv.swap (Fin.last n) p) := hinj.comp (Equiv.injective _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← himg, ← Finset.image_image, Finset.image_univ_equiv]
  · simp [hp]
  · rw [idx _ u p hinjX (by simp [hlast]), mulv]
    funext i
    simp


-- created on 2020-07-26
