import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqMul_1
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetRotaryMatrix.eq.MulCos_Delta.of.Ge.Ge
import Lemma.Tensor.GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt
import Lemma.Tensor.GetRotaryMatrix.eq.MulNegSin_Delta.of.Lt.Ge
import Lemma.Tensor.GetRotaryMatrix.eq.MulSin_Delta.of.Ge.Lt
import Lemma.Tensor.GetRotaryMatrix'.eq.Ite_IteS
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Mul
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.RotaryMatrix'.eq.Stack_Ite_IteS
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Bool List Nat Tensor
set_option maxHeartbeats 20000000


def interleave (d : ℕ) : Tensor ℝ [d + d, d + d] :=
  ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ))) : Tensor ℝ [])) ++
    ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ) + 1)) : Tensor ℝ []))


private def toSplit (d : ℕ) (i : Fin (d + d)) : Fin (d + d) :=
  if (i : ℕ) % 2 = 0 then
    ⟨i / 2, by grind⟩
  else
    ⟨i / 2 + d, by grind⟩


private def fromSplit (d : ℕ) (k : Fin (d + d)) : Fin (d + d) :=
  if h : k < d then
    ⟨2 * k, by grind⟩
  else
    ⟨2 * (k - d) + 1, by grind⟩


private lemma delta_from_eq_delta_to {d : ℕ} (k j : Fin (d + d)) :
    KroneckerDelta (j : ℕ) (fromSplit d k : ℕ) = KroneckerDelta (k : ℕ) (toSplit d j : ℕ) := by
  rw [Delta.eq.Ite, Delta.eq.Ite]
  congr 1
  apply propext
  constructor
  ·
    intro h
    have hj : j = fromSplit d k := Fin.ext h
    have hinv : toSplit d (fromSplit d k) = k := by
      apply Fin.ext
      by_cases hk : k < d
      ·
        have he : (2 * (k : ℕ)) % 2 = 0 := by omega
        simp [fromSplit, toSplit, hk, he]
      ·
        simp [fromSplit, toSplit, hk]
        omega
    have := congrArg (toSplit d) hj
    rw [hinv] at this
    exact congrArg Fin.val this.symm
  ·
    intro h
    have hk : k = toSplit d j := Fin.ext h
    have hinv : fromSplit d (toSplit d j) = j := by
      apply Fin.ext
      by_cases he : (j : ℕ) % 2 = 0
      ·
        have : (j : ℕ) / 2 < d := by grind
        simp [toSplit, fromSplit, he, this]
        exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)
      ·
        have hge : ¬ ((j : ℕ) / 2 + d < d) := by grind
        simp [toSplit, fromSplit, he, hge]
        have h1 : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp he
        omega
    have := congrArg (fromSplit d) hk
    rw [hinv] at this
    exact congrArg Fin.val this.symm


private lemma get_P {d : ℕ} (k j : Fin (d + d)) :
    id (α := Tensor ℝ []) (interleave d)[k][j] =
      (↑(KroneckerDelta (k : ℕ) (toSplit d j : ℕ)) : Tensor ℝ []) := by
  simp only [id, interleave]
  if hk : k < d then
    have hrow :=
      GetAppend.eq.Get.of.Lt (n := d) (m := d) hk
        ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ))) : Tensor ℝ []))
        ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ) + 1)) : Tensor ℝ []))
    have hA :=
      EqGetStack.fin
        (fun i : Fin d => [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ))) : Tensor ℝ []))
        ⟨(k : ℕ), hk⟩
    have hcell :=
      EqGetStack.fin
        (fun j : Fin (d + d) => (↑(KroneckerDelta (j : ℕ) (2 * (k : ℕ))) : Tensor ℝ []))
        j
    have hfrom :
        (↑(KroneckerDelta (j : ℕ) (2 * (k : ℕ))) : Tensor ℝ []) =
          (↑(KroneckerDelta (j : ℕ) (fromSplit d k : ℕ)) : Tensor ℝ []) := by
      unfold fromSplit
      simp [hk]
    refine (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hrow).trans ?_
    refine (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hA).trans ?_
    refine hcell.trans ?_
    apply hfrom.trans
    apply congrArg (fun n : ℕ => (↑n : Tensor ℝ []))
    apply delta_from_eq_delta_to
  else
    have hge : (k : ℕ) ≥ d := Nat.le_of_not_lt hk
    have hrow :=
      GetAppend.eq.Get_Sub.of.GtAdd.Ge (m := d) (n := d) hge k.isLt
        ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ))) : Tensor ℝ []))
        ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ) + 1)) : Tensor ℝ []))
    have hk' : (k : ℕ) - d < d := by
      have := k.isLt
      omega
    have hB :=
      EqGetStack.fin
        (fun i : Fin d => [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ) + 1)) : Tensor ℝ []))
        ⟨(k : ℕ) - d, hk'⟩
    have hcell :=
      EqGetStack.fin
        (fun j : Fin (d + d) => (↑(KroneckerDelta (j : ℕ) (2 * ((k : ℕ) - d) + 1)) : Tensor ℝ []))
        j
    have hfrom :
        (↑(KroneckerDelta (j : ℕ) (2 * ((k : ℕ) - d) + 1)) : Tensor ℝ []) =
          (↑(KroneckerDelta (j : ℕ) (fromSplit d k : ℕ)) : Tensor ℝ []) := by
      unfold fromSplit
      simp [hk]
    refine (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hrow).trans ?_
    refine (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hB).trans ?_
    refine hcell.trans ?_
    apply hfrom.trans
    apply congrArg (fun n : ℕ => (↑n : Tensor ℝ []))
    apply delta_from_eq_delta_to


private lemma get_PT {d : ℕ} (i k : Fin (d + d)) :
    id (α := Tensor ℝ [])
      (cast (congrArg (Tensor ℝ) (a₂ := [d + d, d + d]) (by simp)) (interleave d)ᵀ)[i][k] =
      id (α := Tensor ℝ []) (interleave d)[k][i] := by
  let PT : Tensor ℝ [d + d, d + d] := cast (congrArg (Tensor ℝ) (a₂ := [d + d, d + d]) (by simp)) (interleave d)ᵀ
  have hrow := GetCast.as.Get.of.Eq.GtLength_0.right.fin
    (s' := [d + d, d + d]) (by simp) (by simp) (interleave d)ᵀ i
  have hcell := SEqGetS.of.SEq.GtLength (i := (k : ℕ)) (by simp [Tensor.length]) hrow
  have hT := GetTranspose.eq.Get.fin (interleave d) k i
  simp only [id] at hT ⊢
  have hEq : PT[i][k] = ((interleave d)ᵀ)[i][k] := Eq.of.SEq hcell
  refine hEq.trans ?_
  exact hT


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  rotaryMatrix' θ = ((interleave d)ᵀ @ rotaryMatrix θ) @ interleave d := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  have hR : id (α := Tensor ℝ []) ((((interleave d)ᵀ) @ (rotaryMatrix θ)) @ (interleave d))[i][j] =
      id (α := Tensor ℝ []) (rotaryMatrix θ)[toSplit d i][toSplit d j] := by
    have hL : id (α := Tensor ℝ []) ((((interleave d)ᵀ) @ (rotaryMatrix θ)) @ (interleave d))[i][j] =
        id (α := Tensor ℝ []) (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][toSplit d j] := by
      have hsum := GetDot.eq.Sum_MulGetS (((interleave d)ᵀ) @ (rotaryMatrix θ)) (interleave d) i j
      simp only [id] at hsum ⊢
      refine (rfl : id (α := Tensor ℝ []) ((((interleave d)ᵀ) @ (rotaryMatrix θ)) @ (interleave d))[i][j] =
        ((((interleave d)ᵀ) @ (rotaryMatrix θ)) @ (interleave d))[i, j]).trans ?_
      refine hsum.trans ?_
      refine (Finset.sum_eq_single (toSplit d j) ?off ?mem).trans ?on
      ·
        intro k _ hk
        have hP := get_P (d := d) k j
        simp only [id] at hP
        have hne : (k : ℕ) ≠ (toSplit d j : ℕ) := fun h => hk (Fin.ext h)
        have := congrArg (fun t : Tensor ℝ [] => id (α := Tensor ℝ []) (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][k] * t) hP
        refine this.trans ?_
        simp [Delta.eq.Ite, hne]
        have h0 : (↑(0 : ℕ) : Tensor ℝ []) = (0 : Tensor ℝ []) := Nat.cast_zero
        rw [h0, Tensor.Mul]
        exact mul_zero (id (α := Tensor ℝ []) (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][k])
      ·
        intro h
        exact (h (Finset.mem_univ _)).elim
      ·
        have hP := get_P (d := d) (toSplit d j) j
        simp only [id] at hP
        have := congrArg (fun t : Tensor ℝ [] => id (α := Tensor ℝ []) (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][toSplit d j] * t) hP
        refine this.trans ?_
        simp [Delta.eq.Ite]
        have h1 : (↑(1 : ℕ) : Tensor ℝ []) = (1 : Tensor ℝ []) := Nat.cast_one
        rw [h1, Tensor.Mul]
        exact mul_one (id (α := Tensor ℝ []) (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][toSplit d j])
    have hRT : id (α := Tensor ℝ []) (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][toSplit d j] =
        id (α := Tensor ℝ []) (rotaryMatrix θ)[toSplit d i][toSplit d j] := by
      let PT : Tensor ℝ [d + d, d + d] := cast (congrArg (Tensor ℝ) (by simp)) (interleave d)ᵀ
      have hS : PT ≃ (interleave d)ᵀ := SEqCast.of.Eq (by simp) (interleave d)ᵀ
      have hD := SEqDotS.of.SEq hS (rotaryMatrix θ)
      have hEqDot : (PT) @ (rotaryMatrix θ) = ((interleave d)ᵀ) @ (rotaryMatrix θ) := Eq.of.SEq hD
      have hsum := GetDot.eq.Sum_MulGetS PT (rotaryMatrix θ) i (toSplit d j)
      simp only [id] at hsum ⊢
      refine (congrArg (fun t : Tensor ℝ [d + d, d + d] => id (α := Tensor ℝ []) t[i][toSplit d j]) hEqDot.symm).trans ?_
      refine (rfl : id (α := Tensor ℝ []) ((PT) @ (rotaryMatrix θ))[i][toSplit d j] =
        ((PT) @ (rotaryMatrix θ))[i, toSplit d j]).trans ?_
      refine hsum.trans ?_
      refine (Finset.sum_eq_single (toSplit d i) ?offT ?memT).trans ?onT
      ·
        intro k _ hk
        have hPT := get_PT (d := d) i k
        have hP := get_P (d := d) k i
        simp only [id] at hPT hP
        have hne : (k : ℕ) ≠ (toSplit d i : ℕ) := fun h => hk (Fin.ext h)
        have hδ : id (α := Tensor ℝ []) PT[i][k] = (↑(KroneckerDelta (k : ℕ) (toSplit d i : ℕ)) : Tensor ℝ []) :=
          hPT.trans hP
        have := congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) (rotaryMatrix θ)[k][toSplit d j]) hδ
        refine this.trans ?_
        simp [Delta.eq.Ite, hne]
        have h0 : (↑(0 : ℕ) : Tensor ℝ []) = (0 : Tensor ℝ []) := Nat.cast_zero
        rw [h0, Tensor.Mul]
        exact zero_mul (id (α := Tensor ℝ []) (rotaryMatrix θ)[k][toSplit d j])
      ·
        intro h
        exact (h (Finset.mem_univ _)).elim
      ·
        have hPT := get_PT (d := d) i (toSplit d i)
        have hP := get_P (d := d) (toSplit d i) i
        simp only [id] at hPT hP
        have hδ : id (α := Tensor ℝ []) PT[i][toSplit d i] =
            (↑(KroneckerDelta (toSplit d i : ℕ) (toSplit d i : ℕ)) : Tensor ℝ []) :=
          hPT.trans hP
        have := congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) (rotaryMatrix θ)[toSplit d i][toSplit d j]) hδ
        refine this.trans ?_
        simp [Delta.eq.Ite]
        have h1 : (↑(1 : ℕ) : Tensor ℝ []) = (1 : Tensor ℝ []) := Nat.cast_one
        rw [h1, Tensor.Mul]
        exact one_mul (id (α := Tensor ℝ []) (rotaryMatrix θ)[toSplit d i][toSplit d j])
    simp only [id] at hL hRT ⊢
    exact hL.trans hRT
  simp only [id] at hR ⊢
  apply Eq.trans _ hR.symm
  by_cases hei : (i : ℕ) % 2 = 0
  ·
    by_cases hej : (j : ℕ) % 2 = 0
    ·
      have hL := GetRotaryMatrix'.eq.Ite_IteS θ i j
      simp [toSplit, hei, hej]
      let iC : Fin (d + d) := ⟨(i : ℕ) / 2, by grind⟩
      let jC : Fin (d + d) := ⟨(j : ℕ) / 2, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt θ iC jC (by grind) (by grind)
      simp only [id, iC, jC] at hL hRg ⊢
      refine hL.trans (Eq.trans ?_ hRg.symm)
      have hsucc : ¬((j : ℕ) = (i : ℕ) + 1) := by
        intro h
        omega
      simp [hei, hsucc]
      by_cases hij : (j : ℕ) = (i : ℕ)
      ·
        simp [hij, Delta.eq.Ite]
        have hc : (i : ℕ) / 2 < θ.cos.length := by
          simp [Tensor.length]
          have := i.isLt
          omega
        let c : Tensor ℝ [] := id (α := Tensor ℝ []) (θ.cos[(i : ℕ) / 2]'(hc))
        exact (Tensor.EqMul_1 c).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hij
          have ha2 : 2 * ((i : ℕ) / 2) = (i : ℕ) := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hei)
          have hb2 : 2 * ((j : ℕ) / 2) = (j : ℕ) := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hej)
          omega
        simp [hij, Delta.eq.Ite, hne]
        have hc : (j : ℕ) / 2 < θ.cos.length := by
          simp [Tensor.length]
          have := j.isLt
          omega
        let c : Tensor ℝ [] := id (α := Tensor ℝ []) (θ.cos[(j : ℕ) / 2]'(hc))
        exact (Tensor.EqMul_0'0 c).symm
    ·
      have hL := GetRotaryMatrix'.eq.Ite_IteS θ i j
      simp [toSplit, hei, hej]
      let iC : Fin (d + d) := ⟨(i : ℕ) / 2, by grind⟩
      let jR : Fin (d + d) := ⟨(j : ℕ) / 2 + d, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulNegSin_Delta.of.Lt.Ge θ iC jR (by grind) (by grind)
      simp only [id, iC, jR] at hL hRg ⊢
      refine hL.trans (Eq.trans ?_ hRg.symm)
      have hneij : (j : ℕ) ≠ (i : ℕ) := fun h => hej (h ▸ hei)
      simp [hei, hneij]
      by_cases hs : (j : ℕ) = (i : ℕ) + 1
      ·
        have heq : (i : ℕ) / 2 = ((i : ℕ) + 1) / 2 := by omega
        have hlt : ((i : ℕ) + 1) / 2 < d := by
          have := i.isLt
          omega
        simp [hs, Delta.eq.Ite, heq]
        have hb : ((i : ℕ) + 1) / 2 < θ.sin.length := by
          simp [Tensor.length]
          exact hlt
        let c : Tensor ℝ [] := -(id (α := Tensor ℝ []) (θ.sin[((i : ℕ) + 1) / 2]'(hb)))
        exact (Tensor.EqMul_1 c).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hs
          omega
        simp [hs, Delta.eq.Ite, hne]
        have hsj : (j : ℕ) / 2 < θ.sin.length := by
          simp [Tensor.length]
          have := j.isLt
          omega
        let c : Tensor ℝ [] := -(id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(hsj)))
        exact (Tensor.EqMul_0'0 c).symm
  ·
    by_cases hej : (j : ℕ) % 2 = 0
    ·
      have hL := GetRotaryMatrix'.eq.Ite_IteS θ i j
      simp [toSplit, hei, hej]
      let iR : Fin (d + d) := ⟨(i : ℕ) / 2 + d, by grind⟩
      let jC : Fin (d + d) := ⟨(j : ℕ) / 2, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulSin_Delta.of.Ge.Lt θ iR jC (by grind) (by grind)
      simp only [id, iR, jC] at hL hRg ⊢
      refine hL.trans (Eq.trans ?_ hRg.symm)
      have hneij : (j : ℕ) ≠ (i : ℕ) := fun h => hei (h ▸ hej)
      simp [hei, hneij]
      by_cases hp : (j : ℕ) + 1 = (i : ℕ)
      ·
        have heq : (i : ℕ) / 2 = (j : ℕ) / 2 := by omega
        simp [hp, Delta.eq.Ite, heq]
        have hsj : (j : ℕ) / 2 < θ.sin.length := by
          simp [Tensor.length]
          have := j.isLt
          omega
        let c : Tensor ℝ [] := id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(hsj))
        exact (Tensor.EqMul_1 c).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hp
          omega
        simp [hp, Delta.eq.Ite, hne]
        have hsj : (j : ℕ) / 2 < θ.sin.length := by
          simp [Tensor.length]
          have := j.isLt
          omega
        let c : Tensor ℝ [] := id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(hsj))
        exact (Tensor.EqMul_0'0 c).symm
    ·
      have hL := GetRotaryMatrix'.eq.Ite_IteS θ i j
      simp [toSplit, hei, hej]
      let iR : Fin (d + d) := ⟨(i : ℕ) / 2 + d, by grind⟩
      let jR : Fin (d + d) := ⟨(j : ℕ) / 2 + d, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulCos_Delta.of.Ge.Ge θ iR jR (by grind) (by grind)
      simp only [id, iR, jR] at hL hRg ⊢
      refine hL.trans (Eq.trans ?_ hRg.symm)
      have hpred : ¬((j : ℕ) + 1 = (i : ℕ)) := by
        intro h
        omega
      simp [hei, hpred]
      by_cases hij : (j : ℕ) = (i : ℕ)
      ·
        simp [hij, Delta.eq.Ite]
        have hc : (i : ℕ) / 2 < θ.cos.length := by
          simp [Tensor.length]
          have := i.isLt
          omega
        let c : Tensor ℝ [] := id (α := Tensor ℝ []) (θ.cos[(i : ℕ) / 2]'(hc))
        exact (Tensor.EqMul_1 c).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hij
          omega
        simp [hij, Delta.eq.Ite, hne]
        have hc : (j : ℕ) / 2 < θ.cos.length := by
          simp [Tensor.length]
          have := j.isLt
          omega
        let c : Tensor ℝ [] := id (α := Tensor ℝ []) (θ.cos[(j : ℕ) / 2]'(hc))
        exact (Tensor.EqMul_0'0 c).symm


-- created on 2026-09-04
