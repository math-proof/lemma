import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Image
import sympy.Basic
open Tensor


/--
py (`position_representation.relative.gather`): relative position representations \( K'_{ij} = w^K_{c + \operatorname{clip}(j - i, -c, c)} \), \( V'_{ij} = w^V_{c + \operatorname{clip}(j - i, -c, c)} \)
and the hyperreal masked softmax keeping exactly the \( m \) distinct columns \( d_j \). With \( \delta_{ij} = c + \operatorname{clip}(d_j - i, -c, c) \), row \( i \) of
\( \operatorname{softmax}(A + ([j \in \operatorname{im} d] - 1)\infty)(V + V') \) is infinitely close to
\[
\Bigl[ \sum_{j < m} \frac{e^{a'_{ij}}}{\sum_{k < m} e^{a'_{ik}}}\, (V_{d_j \ell} + w^V_{\delta_{ij} \ell}) \Bigr]_\ell,
\qquad a'_{ij} = \frac{\sum_t Q_{it}(K_{d_j t} + w^K_{\delta_{ij} t})}{\sqrt{d_z}} .
\]
-/
@[main]
private lemma position_representation.relative.gather
  {n d_z : ℕ}
  {m : ℕ}
  {dm : Fin m → Fin n}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
-- given
  (h : (Finset.univ.image dm).card = m)
  (h_m : 0 < m)
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (j ∈ Finset.univ.image dm)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_z] := [j < n] [l < d_z] ((V j l + V' i j l : ℝ) : Tensor ℝ [])
  ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_z]) ≈
    ((([l < d_z] ((∑ j, Real.exp ((∑ t, Q i t * (K (dm j) t + wK (c + max (-c) (min (((dm j).val : ℤ) - i.val) c)) t)) / √(d_z : ℝ)) / (∑ k, Real.exp ((∑ t, Q i t * (K (dm k) t + wK (c + max (-c) (min (((dm k).val : ℤ) - i.val) c)) t)) / √(d_z : ℝ))) * (V (dm j) l + wV (c + max (-c) (min (((dm j).val : ℤ) - i.val) c)) l) : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_z]) : Tensor ℝ* [d_z]) := by
-- proof
  exact DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Image.row h h_m (fun i j => (∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ)) (fun i j l => V j l + V' i j l)
    (fun i j => (∑ t, Q i t * (K (dm j) t + wK (c + max (-c) (min (((dm j).val : ℤ) - i.val) c)) t)) / √(d_z : ℝ))
    (fun i j l => V (dm j) l + wV (c + max (-c) (min (((dm j).val : ℤ) - i.val) c)) l)
    (fun i j => by simp only [h₀]) (fun i j l => by simp only [h₁]) i


/--
py (`position_representation.relative.gather.indexed`): as `position_representation.relative.gather`, but the relative offsets are taken between arbitrary integer positions \( r_j \):
\( K'_{ij} = w^K_{c + \operatorname{clip}(r_j - r_i, -c, c)} \), \( V'_{ij} = w^V_{c + \operatorname{clip}(r_j - r_i, -c, c)} \).
-/
@[main]
private lemma position_representation.relative.gather.indexed
  {n d_z : ℕ}
  {m : ℕ}
  {dm : Fin m → Fin n}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
  {r : Fin n → ℤ}
-- given
  (h : (Finset.univ.image dm).card = m)
  (h_m : 0 < m)
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min (r j - r i) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min (r j - r i) c)) t)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (j ∈ Finset.univ.image dm)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_z] := [j < n] [l < d_z] ((V j l + V' i j l : ℝ) : Tensor ℝ [])
  ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_z]) ≈
    ((([l < d_z] ((∑ j, Real.exp ((∑ t, Q i t * (K (dm j) t + wK (c + max (-c) (min (r (dm j) - r i) c)) t)) / √(d_z : ℝ)) / (∑ k, Real.exp ((∑ t, Q i t * (K (dm k) t + wK (c + max (-c) (min (r (dm k) - r i) c)) t)) / √(d_z : ℝ))) * (V (dm j) l + wV (c + max (-c) (min (r (dm j) - r i) c)) l) : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_z]) : Tensor ℝ* [d_z]) := by
-- proof
  exact DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Image.row h h_m (fun i j => (∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ)) (fun i j l => V j l + V' i j l)
    (fun i j => (∑ t, Q i t * (K (dm j) t + wK (c + max (-c) (min (r (dm j) - r i) c)) t)) / √(d_z : ℝ))
    (fun i j l => V (dm j) l + wV (c + max (-c) (min (r (dm j) - r i) c)) l)
    (fun i j => by simp only [h₀]) (fun i j l => by simp only [h₁]) i


-- created on 2026-09-27