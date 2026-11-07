import Syntax.Fun
import Notation.Fun
import Def.LinearAlgebra.Matrix.BandPart
import Def.LinearAlgebra.Matrix.Ones
import Def.Analysis.Matrix.Softmax
import Instance.LinearAlgebra.Matrix.FunSlice
import Instance.LinearAlgebra.Matrix.IsClose
import Instance.LinearAlgebra.Matrix.Div
import Instance.LinearAlgebra.Matrix.Append
import Instance.LinearAlgebra.Matrix.Dot
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Hyperreal.Any_IsSt.is.NotInfinite
import Lemma.Hyperreal.InfiniteNeg.is.XEqExp_0
import Lemma.Hyperreal.InfinitePos.is.InfiniteNegSub
import Lemma.Hyperreal.InfinitePosInfty
import Lemma.Hyperreal.NeInfty0
import Lemma.Hyperreal.XEq.of.Eq
import Lemma.Hyperreal.XEqSumS.of.All_XEq.OrAll_NotInfinite
import Lemma.Hyperreal.XEqDivS.of.XEq.XEq.NotInfinitesimal
import Lemma.Hyperreal.XEqMulS.of.XEq.XEq.Imp_XEqInvS.Imp_XEqInvS
open Matrix Real Hyperreal Exp List
open scoped Matrix
set_option maxHeartbeats 800000


private lemma notInfinite_coe
-- given
  (r : ℝ) :
-- imply
  ¬(ArchimedeanClass.mk (r : ℝ*) < 0) := by
-- proof
  rw [← Any_IsSt.is.NotInfinite]
  refine ⟨r, ?_⟩
  simp

private lemma exp_coe
-- given
  (r : ℝ) :
-- imply
  Exp.exp (r : ℝ*) = ↑(Real.exp r) := by
-- proof
  dsimp only [Exp.exp]
  rw [Hyperreal.exp]
  exact Filter.Germ.map_const _ r Real.exp

private lemma sqrt_coe
-- given
  (d : ℕ) :
-- imply
  √(d : ℝ*) = ↑(Real.sqrt (d : ℝ)) := by
-- proof
  dsimp only [Root.sqrt]
  have hcoe : (d : ℝ*) = ↑(d : ℝ) := by
    norm_cast
  rw [hcoe]
  exact Filter.Germ.map_const _ (d : ℝ) Real.sqrt

private lemma score_coe
  {d_z : ℕ}
-- given
  (q k : Fin d_z → ℝ) :
-- imply
  (∑ a : Fin d_z, (q a : ℝ*) * (k a : ℝ*)) / √(d_z : ℝ*) =
    ↑((∑ a : Fin d_z, q a * k a) / Real.sqrt (d_z : ℝ)) := by
-- proof
  have hmul (a : Fin d_z) : (q a : ℝ*) * (k a : ℝ*) = ↑(q a * k a) :=
    (Hyperreal.coeRingHom.map_mul (q a) (k a)).symm
  have hsum :
    (∑ a : Fin d_z, (q a : ℝ*) * (k a : ℝ*)) = ↑(∑ a : Fin d_z, q a * k a) := by
    simp_rw [hmul]
    exact (map_sum Hyperreal.coeRingHom.toRingHom (fun a => q a * k a) Finset.univ).symm
  rw [hsum, sqrt_coe]
  exact (map_div₀ Hyperreal.coeRingHom.toRingHom _ _).symm

private lemma exp_neg_infty
-- given
  (r : ℝ) :
-- imply
  Exp.exp ((r : ℝ*) + -(∞)) ≈ 0 := by
-- proof
  have hneg : ((r : ℝ) - ∞) → -∞ :=
    (InfinitePos.is.InfiniteNegSub ∞ r).mp InfinitePosInfty
  have hexp : Exp.exp ((r : ℝ) - ∞) ≈ 0 := by
    simpa [Exp.exp] using (InfiniteNeg.is.XEqExp_0 ((r : ℝ) - ∞)).mp hneg
  have hsub : (r : ℝ*) + -(∞) = (r : ℝ) - ∞ := by
    simp [sub_eq_add_neg]
  rwa [hsub]

private lemma mask_eq
  {k : ℕ}
-- given
  (l : ℕ)
  (i j : Fin k) :
-- imply
  (((Matrix.ones (Fin k) (Fin k) ℝ*).band_part (l - 1) 0) i j - 1) * ∞ =
    if decide (-↑(l - 1) ≤ (j : ℤ) - (i : ℤ) ∧ (j : ℤ) - (i : ℤ) ≤ 0) then
      (0 : ℝ*)
    else
      -(∞) := by
-- proof
  dsimp only [Matrix.band_part, Matrix.ones, Matrix.of_apply]
  split
  ·
    rename_i hcond
    have hdec : decide (-↑(l - 1) ≤ (j : ℤ) - (i : ℤ) ∧ (j : ℤ) - (i : ℤ) ≤ 0) = true := by
      apply decide_eq_true
      obtain ⟨h1, h2, _⟩ := hcond
      exact ⟨h1, by simpa using h2⟩
    rw [hdec]
    simp
  ·
    rename_i hcond
    have hdec : decide (-↑(l - 1) ≤ (j : ℤ) - (i : ℤ) ∧ (j : ℤ) - (i : ℤ) ≤ 0) = false := by
      apply decide_eq_false
      intro hc
      apply hcond
      exact ⟨hc.1, by simpa using hc.2, one_dvd _⟩
    rw [hdec]
    simp [sub_eq_add_neg]

private lemma window_bound
  {n start t : ℕ}
-- given
  (hs : start ≤ n)
  (ht : t < n - start + 1) :
-- imply
  start + t < n + 1 := by
-- proof
  simpa [Nat.add_sub_of_le hs] using
    Nat.lt_succ_of_le (Nat.add_le_add_left (Nat.le_of_lt_succ ht) start)

private lemma sum_window
  [AddCommMonoid M]
  {n start w : ℕ}
  {F : Fin (n + 1) → M}
-- given
  (hs : start ≤ n)
  (hw : w = n - start)
  (h0 : ∀ j : Fin (n + 1), ((j : ℕ) < start) → F j = 0) :
-- imply
  ∑ j : Fin (n + 1), F j =
    ∑ t : Fin (w + 1),
      F ⟨start + (t : ℕ),
        window_bound hs (Eq.mp (congrArg (fun x => (t : ℕ) < x + 1) hw) t.isLt)⟩ := by
-- proof
  suffices hraw :
    ∑ j : Fin (n + 1), F j =
      ∑ t : Fin (n - start + 1),
        F ⟨start + (t : ℕ), window_bound hs t.isLt⟩ by
    exact hraw.trans (Fintype.sum_equiv (finCongr (by rw [hw]))
      (fun t => F ⟨start + (t : ℕ), window_bound hs t.isLt⟩)
      (fun t => F ⟨start + (t : ℕ),
        window_bound hs (Eq.mp (congrArg (fun x => (t : ℕ) < x + 1) hw) t.isLt)⟩)
      (fun t => by
        simp))
  let s : Set (Fin (n + 1)) := {j | start ≤ (j : ℕ)}
  have hsum : ∑ j, F j = ∑ j : s, F ↑j :=
    Finset.sum_congr_set s F (fun j => F ↑j) (fun _ _ => rfl)
      (fun j hj => h0 j (Nat.lt_of_not_le (by simpa [s] using hj)))
  let e : Fin (n - start + 1) ≃ s :=
    { toFun := fun t =>
        ⟨⟨start + (t : ℕ), window_bound hs t.isLt⟩, Nat.le_add_right _ _⟩
      invFun := fun j =>
        ⟨j.1.1 - start, by
          exact Nat.lt_succ_of_le
            (Nat.sub_le_sub_right (Nat.le_of_lt_succ j.1.isLt) start)⟩
      left_inv := fun t => by
        ext
        simp
      right_inv := fun j => by
        ext
        exact Nat.add_sub_of_le j.2 }
  have hcomp : ∑ j : s, F ↑j = ∑ t, F ↑(e t) :=
    (Equiv.sum_comp e (fun j => F ↑j)).symm
  rw [hsum, hcomp]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1

@[path]
private lemma main
  [NeZero (l : ℕ)]
  {n d_z : ℕ}
  {Z : (k : ℕ) ⇀ Matrix (Fin k) (Fin d_z) ℝ}
  {Q K V : ℕ ⇀ Fin d_z ⇀ ℝ}
-- given
  (h : ∀ n,
    (Z[n] : Matrix (Fin n) (Fin d_z) ℝ*) ≈
      (((Q[:n] : Matrix (Fin n) (Fin d_z) ℝ) : Matrix (Fin n) (Fin d_z) ℝ*) *
          ((K[:n] : Matrix (Fin n) (Fin d_z) ℝ) : Matrix (Fin n) (Fin d_z) ℝ*)ᵀ / √(d_z : ℝ*) +
        (((Matrix.ones (Fin n) (Fin n) ℝ*).band_part (l - 1) 0) - 1) * ∞).softmax 1 *
        ((V[:n] : Matrix (Fin n) (Fin d_z) ℝ) : Matrix (Fin n) (Fin d_z) ℝ*)) :
-- imply
  let start := n + 1 - l
  let w := ((⟨start, n, 1⟩ : Slice).length n)
  let KT : Matrix (Fin d_z) (Fin w) ℝ* :=
    (Matrix.of fun (t : Fin w) a => (K[start + (t : ℕ)][a] : ℝ*))ᵀ
  let kT : Matrix (Fin d_z) (Fin 1) ℝ* :=
    (Matrix.of fun (_ : Fin 1) a => (K[n][a] : ℝ*))ᵀ
  let row : Fin d_z → ℝ* :=
    ((Q[n] @ (KT ++ kT) / √(d_z : ℝ*)).softmax 1 *
      ((Matrix.of fun (t : Fin w) a => (V[start + (t : ℕ)][a] : ℝ*)) ++
        (Matrix.of fun (_ : Fin 1) a => (V[n][a] : ℝ*)))) ⟨0, by decide⟩
  (Z[n + 1] : Matrix (Fin (n + 1)) (Fin d_z) ℝ*) ≈
    (Z[n] : Matrix (Fin n) (Fin d_z) ℝ*) ++ Matrix.of (fun (_ : Fin 1) => row) := by
-- proof
  extract_lets start w KT kT row
  intro i a
  have hl : 0 < l := NeZero.pos l
  let raw (p q : ℕ) : ℝ :=
    (∑ b : Fin d_z, Q[p][b] * K[q][b]) / Real.sqrt (d_z : ℝ)
  let keep (u v : ℤ) : Bool :=
    decide (-↑(l - 1) ≤ v - u ∧ v - u ≤ 0)
  let e (p q : ℕ) : ℝ :=
    if keep (p : ℤ) (q : ℤ) then Real.exp (raw p q) else 0
  let D (k : ℕ) (i : Fin k) : ℝ :=
    ∑ j : Fin k, e (i : ℕ) (j : ℕ)
  let ideal (k : ℕ) (i : Fin k) (a : Fin d_z) : ℝ* :=
    ∑ j : Fin k,
      ↑(e (i : ℕ) (j : ℕ)) / ↑(D k i) * (V[(j : ℕ)][a] : ℝ*)
  have attn_ok (k : ℕ) (i : Fin k) (a : Fin d_z) :
    (Z[k] : Matrix (Fin k) (Fin d_z) ℝ*) i a ≈ ideal k i a := by
    have hk := h k
    let S : Matrix (Fin k) (Fin k) ℝ* :=
      ((Q[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*) *
          ((K[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*)ᵀ / √(d_z : ℝ*) +
        (((Matrix.ones (Fin k) (Fin k) ℝ*).band_part (l - 1) 0) - 1) * ∞
    refine (hk i a).trans ?_
    have hcast (j : Fin k) : (j : ℤ) = ((j : ℕ) : ℤ) := by
      simp
    have hdot (j : Fin k) :
      (((Q[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*) *
          ((K[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*)ᵀ) i j =
        ∑ b : Fin d_z, (Q[(i : ℕ)][b] : ℝ*) * (K[(j : ℕ)][b] : ℝ*) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.transpose_apply]
      simp [Matrix.ofFunSlicePrefix, Matrix.of_apply, Fun.getSlice,
        Function.getSlice, FunSlice.slice]
    have hS (j : Fin k) :
      S i j =
        ↑(raw (i : ℕ) (j : ℕ)) +
          (((Matrix.ones (Fin k) (Fin k) ℝ*).band_part (l - 1) 0) i j - 1) * ∞ := by
      simp only [S, Matrix.add_apply, Matrix.div_apply, Matrix.mul_scalar_apply,
        Matrix.sub_scalar_apply]
      rw [hdot j, score_coe (fun b => Q[(i : ℕ)][b]) (fun b => K[(j : ℕ)][b])]
    have hexp (j : Fin k) : Exp.exp (S i j) ≈ ↑(e (i : ℕ) (j : ℕ)) := by
      rw [hS j, mask_eq l i j, hcast i, hcast j]
      have hk :
        keep ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) =
          decide (-↑(l - 1) ≤ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ∧
            ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ≤ 0) := by
        simp only [keep]
      rw [← hk]
      dsimp only [e]
      split_ifs with hkeep
      ·
        simp only [add_zero]
        exact XEq.of.Eq (exp_coe (raw (i : ℕ) (j : ℕ)))
      ·
        exact exp_neg_infty (raw (i : ℕ) (j : ℕ))
    have hdiag : keep ((i : ℕ) : ℤ) ((i : ℕ) : ℤ) = true := by
      simp only [keep, decide_eq_true_iff]
      omega
    have hediag : e (i : ℕ) (i : ℕ) = Real.exp (raw (i : ℕ) (i : ℕ)) := by
      simp [e, hdiag]
    have hnn (j : Fin k) : 0 ≤ e (i : ℕ) (j : ℕ) := by
      simp [e]
      split
      ·
        exact (Real.exp_pos _).le
      ·
        rfl
    have hpos : 0 < D k i := by
      exact lt_of_lt_of_le (hediag.symm ▸ Real.exp_pos _)
        (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))
    have hsumexp : (∑ j : Fin k, Exp.exp (S i j)) ≈ ↑(D k i) := by
      have hnot (j : Fin k) := notInfinite_coe (e (i : ℕ) (j : ℕ))
      have hsum :=
        XEqSumS.of.All_XEq.OrAll_NotInfinite (Or.inl hnot) hexp
      refine hsum.trans (XEq.of.Eq ?_)
      have hDe : (∑ j : Fin k, e (i : ℕ) (j : ℕ)) = D k i := by
        simp [D]
      rw [← hDe]
      exact (map_sum Hyperreal.coeRingHom.toRingHom
        (fun j : Fin k => e (i : ℕ) (j : ℕ)) Finset.univ).symm
    have hden : ¬(0 < ArchimedeanClass.mk (D k i : ℝ*)) :=
      NotInfinitesimal.of.Ne_0 (ne_of_gt hpos)
    have hdiv (j : Fin k) :
      Exp.exp (S i j) / ∑ j' : Fin k, Exp.exp (S i j') ≈
        ↑(e (i : ℕ) (j : ℕ)) / ↑(D k i) :=
      XEqDivS.of.XEq.XEq.NotInfinitesimal hden (hexp j) hsumexp
    have hweight (j : Fin k) :
      ↑(e (i : ℕ) (j : ℕ)) / ↑(D k i) =
        ↑(e (i : ℕ) (j : ℕ) / D k i) :=
      rfl
    have hprod (j : Fin k) :
      ↑(e (i : ℕ) (j : ℕ)) / ↑(D k i) * (V[(j : ℕ)][a] : ℝ*) =
        ↑(e (i : ℕ) (j : ℕ) / D k i * V[(j : ℕ)][a]) := by
      rw [hweight j]
      rfl
    have hV (j : Fin k) :
      ((V[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*) j a =
        (V[(j : ℕ)][a] : ℝ*) := by
      simp [Matrix.ofFunSlicePrefix, Matrix.of_apply, Fun.getSlice,
        Function.getSlice, FunSlice.slice]
    have hmul (j : Fin k) :
      Exp.exp (S i j) / (∑ j' : Fin k, Exp.exp (S i j')) *
          ((V[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*) j a ≈
        ↑(e (i : ℕ) (j : ℕ)) / ↑(D k i) * (V[(j : ℕ)][a] : ℝ*) := by
      rw [hV j]
      apply XEqMulS.of.XEq.XEq.Imp_XEqInvS.Imp_XEqInvS
      ·
        intro hinf
        exact absurd hinf (notInfinite_coe V[(j : ℕ)][a])
      ·
        intro hinf
        exact absurd hinf (notInfinite_coe (e (i : ℕ) (j : ℕ) / D k i))
      ·
        exact hdiv j
      ·
        exact XEq.of.Eq rfl
    have hsoft (j : Fin k) :
      (S.softmax 1) i j = Exp.exp (S i j) / ∑ j' : Fin k, Exp.exp (S i j') := by
      unfold Matrix.softmax
      rw [dite_eq_right (by decide : (1 : ℕ) ≠ 0)]
      simp [Matrix.of_apply]
    have hmulM :
      (S.softmax 1 * ((V[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*)) i a =
        ∑ j : Fin k,
          Exp.exp (S i j) / (∑ j' : Fin k, Exp.exp (S i j')) *
            ((V[:k] : Matrix (Fin k) (Fin d_z) ℝ) : Matrix (Fin k) (Fin d_z) ℝ*) j a := by
      simp [Matrix.mul_apply, hsoft]
    have hnotB (j : Fin k) :
      ¬(ArchimedeanClass.mk
          (↑(e (i : ℕ) (j : ℕ)) / ↑(D k i) * (V[(j : ℕ)][a] : ℝ*)) < 0) := by
      rw [hprod j]
      exact notInfinite_coe _
    rw [hmulM]
    dsimp only [ideal]
    exact XEqSumS.of.All_XEq.OrAll_NotInfinite (Or.inl hnotB) hmul
  if hlt : (i : ℕ) < n then
    have hblock :
      ((Z[n] : Matrix (Fin n) (Fin d_z) ℝ*) ++ Matrix.of (fun (_ : Fin 1) => row)) i a =
        (Z[n] ⟨(i : ℕ), hlt⟩ a : ℝ*) := by
      have hidx : Fin.castAdd 1 ⟨(i : ℕ), hlt⟩ = i := by
        ext
        simp
      have hL := append_row_left
        (Z[n] : Matrix (Fin n) (Fin d_z) ℝ*) (Matrix.of (fun (_ : Fin 1) => row)) ⟨(i : ℕ), hlt⟩
      have hentry := congrFun (hidx ▸ hL) a
      erw [Matrix.of_apply] at hentry
      exact hentry
    have hcoe :
      (Z[n] : Matrix (Fin n) (Fin d_z) ℝ*) ⟨(i : ℕ), hlt⟩ a =
        (Z[n] ⟨(i : ℕ), hlt⟩ a : ℝ*) := by
      erw [Matrix.of_apply]
    have hideal :
      ideal (n + 1) i a = ideal n ⟨(i : ℕ), hlt⟩ a := by
      have hlast : e (i : ℕ) n = 0 := by
        have hnot : keep ((i : ℕ) : ℤ) (n : ℤ) = false := by
          simp only [keep, decide_eq_false_iff_not]
          intro hc
          omega
        simp [e, hnot]
      have hD : D (n + 1) i = D n ⟨(i : ℕ), hlt⟩ := by
        simp only [D]
        rw [Fin.sum_univ_castSucc]
        simp [hlast, Fin.val_castSucc, Fin.val_last]
      simp only [ideal]
      rw [Fin.sum_univ_castSucc, hD]
      simp [hlast, Fin.val_castSucc, Fin.val_last]
    have hBig := attn_ok (n + 1) i a
    have hSmall := attn_ok n ⟨(i : ℕ), hlt⟩ a
    rw [hblock, ← hcoe]
    exact hBig.trans (hideal.symm ▸ hSmall.symm)
  else
    have hblock :
      ((Z[n] : Matrix (Fin n) (Fin d_z) ℝ*) ++ Matrix.of (fun (_ : Fin 1) => row)) i a =
        row a := by
      refine congrFun ((?_ : Fin.natAdd n (0 : Fin 1) = i) ▸ append_row_right
        (Z[n] : Matrix (Fin n) (Fin d_z) ℝ*) (Matrix.of (fun (_ : Fin 1) => row)) (0 : Fin 1)) a
      ext
      simp [Fin.natAdd]
      have := hlt
      have := i.isLt
      omega
    have hi : (i : ℕ) = n := by
      have := i.isLt
      omega
    have hs : start ≤ n := by
      omega
    have hw : w = n - start := by
      simpa [w, min_self] using LengthSlice.eq.SubMin n n start
    have hsw : start + w = n := by
      rw [hw]
      omega
    have hkeep_iff (j : Fin (n + 1)) :
      keep (n : ℤ) (j : ℤ) = true ↔ start ≤ (j : ℕ) := by
      simp only [keep, decide_eq_true_iff]
      have hj := j.isLt
      constructor
      ·
        intro hc
        omega
      ·
        intro hc
        omega
    let F (j : Fin (n + 1)) : ℝ* :=
      ↑(e (i : ℕ) (j : ℕ)) / ↑(D (n + 1) i) * (V[(j : ℕ)][a] : ℝ*)
    have hF0 (j : Fin (n + 1)) (hj : (j : ℕ) < start) : F j = 0 := by
      have hkf : keep (n : ℤ) (j : ℤ) = false := by
        cases hkj : keep (n : ℤ) (j : ℤ)
        ·
          rfl
        ·
          have := (hkeep_iff j).mp hkj
          omega
      simp [F, e, hkf, hi]
    have hsumF := sum_window (F := F) hs hw hF0
    have hDe :
      D (n + 1) i = ∑ t : Fin (w + 1), Real.exp (raw n (start + (t : ℕ))) := by
      simp only [D, hi]
      have h0e (j : Fin (n + 1)) (hj : (j : ℕ) < start) : e n (j : ℕ) = 0 := by
        have hkf : keep (n : ℤ) (j : ℤ) = false := by
          cases hkj : keep (n : ℤ) (j : ℤ)
          ·
            rfl
          ·
            have := (hkeep_iff j).mp hkj
            omega
        simp [e, hkf]
      have hsume := sum_window (F := fun j => e n (j : ℕ)) hs hw h0e
      rw [hsume]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hkt : keep (n : ℤ) (↑(start + (t : ℕ))) = true := by
        simp only [Nat.cast_add]
        exact (hkeep_iff ⟨start + (t : ℕ), by have := t.isLt; omega⟩).mpr
          (Nat.le_add_right _ _)
      simp only [e]
      rw [hkt]
      simp
    have hkey (t : Fin (w + 1)) (b : Fin d_z) :
      (KT ++ kT) b t = (K[start + (t : ℕ)][b] : ℝ*) := by
      if ht : (t : ℕ) < w then
        have hidx : Fin.castAdd 1 ⟨(t : ℕ), ht⟩ = t := by
          ext
          simp
        rw [← hidx, append_col_left]
        simp [KT, Matrix.transpose_apply, Matrix.of_apply]
      else
        have htw : (t : ℕ) = w := by
          have := t.isLt
          omega
        have hidx : Fin.natAdd w (0 : Fin 1) = t := by
          ext
          simp [Fin.natAdd, htw]
        rw [← hidx, append_col_right]
        simp [kT, Matrix.transpose_apply, Matrix.of_apply, hsw]
    have hscore (t : Fin (w + 1)) :
      (Q[n] @ (KT ++ kT) / √(d_z : ℝ*)) ⟨0, by decide⟩ t =
        ↑(raw n (start + (t : ℕ))) := by
      simp only [Fun.dot_matrix_apply, Matrix.div_apply, hkey t, raw]
      exact score_coe (fun b => Q[n][b]) (fun b => K[start + (t : ℕ)][b])
    have hexpScore (t : Fin (w + 1)) :
      Exp.exp ((Q[n] @ (KT ++ kT) / √(d_z : ℝ*)) ⟨0, by decide⟩ t) =
        ↑(Real.exp (raw n (start + (t : ℕ)))) := by
      rw [hscore t, exp_coe]
    have hsumScore :
      (∑ t : Fin (w + 1),
          Exp.exp ((Q[n] @ (KT ++ kT) / √(d_z : ℝ*)) ⟨0, by decide⟩ t)) =
        ↑(D (n + 1) i) := by
      simp_rw [hexpScore]
      have hmap :=
        (map_sum Hyperreal.coeRingHom.toRingHom
          (fun t : Fin (w + 1) => Real.exp (raw n (start + (t : ℕ)))) Finset.univ).symm
      rwa [hDe]
    have hsm (t : Fin (w + 1)) :
      ((Q[n] @ (KT ++ kT) / √(d_z : ℝ*)).softmax 1) ⟨0, by decide⟩ t =
        Exp.exp ((Q[n] @ (KT ++ kT) / √(d_z : ℝ*)) ⟨0, by decide⟩ t) /
          ∑ t' : Fin (w + 1),
            Exp.exp ((Q[n] @ (KT ++ kT) / √(d_z : ℝ*)) ⟨0, by decide⟩ t') := by
      unfold Matrix.softmax
      rw [dite_eq_right (by decide : (1 : ℕ) ≠ 0)]
      simp [Matrix.of_apply]
    have hVw (t : Fin (w + 1)) :
      ((Matrix.of fun (s : Fin w) b => (V[start + (s : ℕ)][b] : ℝ*)) ++
        (Matrix.of fun (_ : Fin 1) b => (V[n][b] : ℝ*))) t a =
        (V[start + (t : ℕ)][a] : ℝ*) := by
      if ht : (t : ℕ) < w then
        have hidx : Fin.castAdd 1 ⟨(t : ℕ), ht⟩ = t := by
          ext
          simp
        have hL := append_row_left
          (Matrix.of fun (s : Fin w) b => (V[start + (s : ℕ)][b] : ℝ*))
          (Matrix.of fun (_ : Fin 1) b => (V[n][b] : ℝ*)) ⟨(t : ℕ), ht⟩
        have hentry := congrFun (hidx ▸ hL) a
        simpa [Matrix.of_apply] using hentry
      else
        have htw : (t : ℕ) = w := by
          have := t.isLt
          omega
        have hidx : Fin.natAdd w (0 : Fin 1) = t := by
          ext
          simp [Fin.natAdd, htw]
        have hR := append_row_right
          (Matrix.of fun (s : Fin w) b => (V[start + (s : ℕ)][b] : ℝ*))
          (Matrix.of fun (_ : Fin 1) b => (V[n][b] : ℝ*)) (0 : Fin 1)
        have hentry := congrFun (hidx ▸ hR) a
        simpa [Matrix.of_apply, htw, hsw] using hentry
    have hewin (t : Fin (w + 1)) :
      e (i : ℕ) (start + (t : ℕ)) = Real.exp (raw n (start + (t : ℕ))) := by
      have hkt : keep ((i : ℕ) : ℤ) (↑(start + (t : ℕ))) = true := by
        rw [hi]
        simp only [Nat.cast_add]
        exact (hkeep_iff ⟨start + (t : ℕ), by have := t.isLt; omega⟩).mpr
          (Nat.le_add_right _ _)
      simp only [e]
      rw [hkt]
      simp [hi]
    have hterm (t : Fin (w + 1)) :
      F ⟨start + (t : ℕ), by have := t.isLt; omega⟩ =
        ((Q[n] @ (KT ++ kT) / √(d_z : ℝ*)).softmax 1) ⟨0, by decide⟩ t *
          (V[start + (t : ℕ)][a] : ℝ*) := by
      simp only [F]
      rw [hewin t, hsm t, hexpScore t, hsumScore]
    have hrow : ideal (n + 1) i a = row a := by
      have hsumI : ideal (n + 1) i a = ∑ j, F j := by
        simp [ideal, F]
      rw [hsumI, hsumF]
      simp only [row, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hVw t]
      exact hterm t
    rw [hblock, ← hrow]
    exact attn_ok (n + 1) i a


-- created on 2026-11-07
