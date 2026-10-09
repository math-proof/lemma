import Lemma.Tensor.Dot.eq.Add.of.Eq_Mul.Eq_Mul.Eq_Block
import Lemma.Tensor.EqDot.of.Eq_Mul.Eq_Mul.Eq_Block
import sympy.Basic
open Matrix


/--
2D rotary position encoding (row index \( r \), column index \( c \)).
The softmax attention of the rotated queries and keys equals the attention whose logits depend only on the relative position:
\[
\operatorname{softmax}\left(\frac{(R_i Q_i) \cdot (R_t K_t)}{\sqrt{d}}\right) V = \frac{\sum_t V_{t,j} \exp\left(\frac{[A, B] \cdot [\cos \theta, \sin \theta]}{\sqrt{d}}\right)}{\sum_s \exp\left(\frac{(R_i Q_i) \cdot (R_s K_s)}{\sqrt{d}}\right)}
\]
-/
@[path]
private lemma plane
  {n mr mc : ℕ}
  {br bc lr lc : ℝ}
  {θr : ℤ → Fin mr → ℝ}
  {θc : ℤ → Fin mc → ℝ}
  {R : ℤ → ℤ → Matrix (Fin (mr + mc) ⊕ Fin (mr + mc)) (Fin (mr + mc) ⊕ Fin (mr + mc)) ℝ}
  {r c : Fin n → ℤ}
  {Q K V : Fin n → Fin (mr + mc) ⊕ Fin (mr + mc) → ℝ}
-- given
  (h₀ : ∀ i h, θr i h = lr * i / br ^ ((h : ℝ) / mr))
  (h₁ : ∀ j h, θc j h = lc * j / bc ^ ((h : ℝ) / mc))
  (h₂ : ∀ i j, R i j = Matrix.fromBlocks (Matrix.diagonal fun k => Real.cos (Fin.append (θr i) (θc j) k)) (-Matrix.diagonal fun k => Real.sin (Fin.append (θr i) (θc j) k)) (Matrix.diagonal fun k => Real.sin (Fin.append (θr i) (θc j) k)) (Matrix.diagonal fun k => Real.cos (Fin.append (θr i) (θc j) k))) :
-- imply
  let S (i t : Fin n) : ℝ := ((R (r i) (c i) *ᵥ Q i) ⬝ᵥ (R (r t) (c t) *ᵥ K t)) / Real.sqrt (2 * (mr + mc))
  let θ (i t : Fin n) : Fin (mr + mc) → ℝ := Fin.append (θr (r t - r i)) (θc (c t - c i))
  (Matrix.of fun i t => Real.exp (S i t) / ∑ s, Real.exp (S i s)) * Matrix.of V =
    Matrix.of fun i j => (∑ t, V t j * Real.exp ((∑ a, ((K t (Sum.inl a) * Q i (Sum.inl a) + K t (Sum.inr a) * Q i (Sum.inr a)) * Real.cos (θ i t a) + (K t (Sum.inl a) * Q i (Sum.inr a) - K t (Sum.inr a) * Q i (Sum.inl a)) * Real.sin (θ i t a))) / Real.sqrt (2 * (mr + mc)))) / ∑ s, Real.exp (S i s) := by
-- proof
  intro S θ
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  have h_rel : ∀ i' j' i j : ℤ, (R i' j')ᵀ * R i j = R (i - i') (j - j') :=
    fun i' j' i j => Tensor.EqDot.of.Eq_Mul.Eq_Mul.Eq_Block.position_representation.plane h₀ h₁ h₂
  have h_mul := Tensor.Dot.eq.Add.of.Eq_Mul.Eq_Mul.Eq_Block.position_representation.plane (r := fun _ => r t - r i) (c := fun _ => c t - c i) (t := 0) h₀ h₁ h₂ (x := K t)
  have h_dot : ((R (r i) (c i) *ᵥ Q i) ⬝ᵥ (R (r t) (c t) *ᵥ K t)) = ∑ a, ((K t (Sum.inl a) * Q i (Sum.inl a) + K t (Sum.inr a) * Q i (Sum.inr a)) * Real.cos (θ i t a) + (K t (Sum.inl a) * Q i (Sum.inr a) - K t (Sum.inr a) * Q i (Sum.inl a)) * Real.sin (θ i t a)) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h_rel, h_mul]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [θ]
    ring
  have : S i t = (∑ a, ((K t (Sum.inl a) * Q i (Sum.inl a) + K t (Sum.inr a) * Q i (Sum.inr a)) * Real.cos (θ i t a) + (K t (Sum.inl a) * Q i (Sum.inr a) - K t (Sum.inr a) * Q i (Sum.inl a)) * Real.sin (θ i t a))) / Real.sqrt (2 * (mr + mc)) := by
    simp only [S, h_dot]
  rw [← this]
  ring


-- created on 2023-09-18
-- updated on 2023-09-20
