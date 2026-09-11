import Lemma.Tensor.DetInterleave.eq.MulPowNeg1Sub_Det
open Matrix Tensor
set_option maxHeartbeats 800000


private lemma pow_neg_one_step (d : ℕ) (hd : 1 < d) :
    Mul.mul ((-1 : Tensor ℝ []) ^ (d - 1)) ((-1 : Tensor ℝ []) ^ ((d - 1) / 2)) =
      (-1 : Tensor ℝ []) ^ (d / 2) := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd d
  · rw [hk]
    have hk0 : 0 < k := by omega
    have h2 : k + k = 2 * k := (two_mul k).symm
    simp [h2]
    have hodd : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
    have hs : (-1 : Tensor ℝ []) ^ (2 * k - 1) = -1 := Odd.neg_one_pow hodd
    have hdiv : (2 * k - 1) / 2 = k - 1 := by omega
    rw [hs, hdiv]
    obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd k
    · have hkm : Odd (k - 1) := ⟨m - 1, by omega⟩
      have h1 : (-1 : Tensor ℝ []) ^ (k - 1) = -1 := Odd.neg_one_pow hkm
      have h2' : (-1 : Tensor ℝ []) ^ k = 1 := Even.neg_one_pow ⟨m, hm⟩
      simp [h1, h2']
      exact (neg_mul_neg (1 : Tensor ℝ []) 1).trans (one_mul 1)
    · have hkm : Even (k - 1) := ⟨m, by omega⟩
      have h1 : (-1 : Tensor ℝ []) ^ (k - 1) = 1 := Even.neg_one_pow hkm
      have h2' : (-1 : Tensor ℝ []) ^ k = -1 := Odd.neg_one_pow ⟨m, hm⟩
      simp [h1, h2']
      exact mul_one (-1 : Tensor ℝ [])
  · rw [hk]
    have he : Even (2 * k) := even_two_mul k
    have hs : (-1 : Tensor ℝ []) ^ (2 * k + 1 - 1) = 1 := by
      change (-1 : Tensor ℝ []) ^ (2 * k) = 1
      exact Even.neg_one_pow he
    have hdiv : (2 * k + 1 - 1) / 2 = k := by omega
    have hgoal : (2 * k + 1) / 2 = k := by omega
    rw [hs, hdiv, hgoal]
    exact one_mul _


/--
Even/odd gather \(\boldsymbol{P}=\mathrm{interleave}\,d\) has determinant
\(\det\boldsymbol{P}=(-1)^{d/2}\) (Nat floor division).

Proof plan (row shift / induction): left-multiply by `ShiftMatrix(2d, d, 1)`
moves row `d` to index `1` with sign `(-1)^(d-1)`; the leading `2×2` is `I`
and the trailing block is `interleave (d-1)`, so
`det P_d = (-1)^(d-1) · det P_{d-1}`.
-/
@[main]
private lemma main
  {d : ℕ} :
-- imply
  (interleave d).det = (-1) ^ (d / 2) := by
-- proof
  induction d with
  | zero =>
    apply Eq.trans (Det.eq.DetToMatrix (interleave 0))
    rw [Matrix.det_fin_zero]
    rfl
  | succ d ih =>
    cases d with
    | zero =>
      apply Eq.trans (Det.eq.DetToMatrix (interleave 1))
      have hP : (interleave 1).toMatrix = (1 : Matrix (Fin 2) (Fin 2) (Tensor ℝ [])) := by
        ext i j
        have h := GetInterleave.eq.Delta_ToSplit i j
        simp only [Tensor.toMatrix, GetElem.getElem] at h ⊢
        rw [h, Delta.eq.Ite]
        simp only [Fin.toSplit, Matrix.one_apply]
        have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
          have := i.isLt
          omega
        have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by
          have := j.isLt
          omega
        obtain hi0 | hi1 := hi01 <;> obtain hj0 | hj1 := hj01
        · simp [hi0, hj0, Fin.ext_iff]
        · simp [hi0, hj1, Fin.ext_iff]
        · simp [hi1, hj0, Fin.ext_iff]
        · simp [hi1, hj1, Fin.ext_iff]
      rw [hP, det_one]
      rfl
    | succ n =>
      have hd : 1 < n + 2 := by omega
      apply Eq.trans (Det.eq.DetToMatrix (interleave (n + 2)))
      have hrec := DetInterleave.eq.MulPowNeg1Sub_Det (n + 2) hd
      have hdim : n + 2 - 1 = n + 1 := Nat.add_sub_cancel (n + 1) 1
      simp [hdim] at hrec
      rw [hrec]
      have ih' : (interleave (n + 1)).toMatrix.det = (-1) ^ ((n + 1) / 2) :=
        (Det.eq.DetToMatrix (interleave (n + 1))).symm.trans ih
      rw [ih']
      exact pow_neg_one_step (n + 2) hd


-- created on 2026-09-07
-- updated on 2026-09-11
