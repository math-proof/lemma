import sympy.core.relational
import Lemma.Bool.Ne.is.NotEq
import Lemma.Int.FModNeg.eq.Ite_0Sub_FMod
import Lemma.Int.FModNeg.eq.Zero.of.FMod.eq.Zero
import Lemma.Int.FModSub.eq.FModNeg.of.FMod.eq.Zero
import Lemma.Int.Any_Eq_AddMul.of.EqFMod
import Lemma.Int.SubAdd.eq.Add_Sub
import Lemma.Int.FModAddMul.eq.FMod
import Lemma.Int.FModNegSign.eq.Sub_Sign
import Lemma.Int.AddSub.eq.Sub_Sub
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Nat.Add
import Lemma.Int.EqFMod.of.Mul_Add_Sign.lt.Zero
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Int.LeSign.of.Gt_0
import Lemma.Set.MulSubS.le.Zero.of.In_Icc
import Lemma.Nat.Mul
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Algebra.NotGt.is.Le
import Lemma.Set.FMod.in.IccSign.of.FMod.ne.Zero.Gt_0
import Lemma.Set.FMod.in.Icc_Sign.of.FMod.ne.Zero.Lt_0
open Algebra Set Bool Int Nat


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  (-n).fmod d + (n - sign d).fmod d = (-sign d).fmod d := by
-- proof
  by_cases h_d : d = 0
  ·
    rw [h_d]
    norm_num
  ·
    have h_d := Ne.of.NotEq h_d
    have h_Ite := FModNeg.eq.Ite_0Sub_FMod (n := n) (d := d)
    by_cases h_nd : n.fmod d = 0
    ·
      simp [h_nd] at h_Ite
      rw [h_Ite]
      simp
      have := FModNeg.eq.Zero.of.FMod.eq.Zero h_Ite
      rw [EqNegNeg] at this
      apply FModSub.eq.FModNeg.of.FMod.eq.Zero this
    ·
      simp [h_nd] at h_Ite
      have h_nd := Ne.of.NotEq h_nd
      rw [h_Ite]
      denote h_r : r = n.fmod d
      rw [← h_r]
      let ⟨q, h_n⟩ := Any_Eq_AddMul.of.EqFMod h_r.symm
      rw [h_n]
      rw [SubAdd.eq.Add_Sub]
      rw [FModAddMul.eq.FMod]
      rw [FModNegSign.eq.Sub_Sign]
      rw [AddSub.eq.Sub_Sub]
      simp
      apply EqSub.of.Eq_Add
      rw [Add.comm]
      apply Eq_Add.of.EqSub
      apply Eq.symm
      apply EqFMod.of.Mul_Add_Sign.lt.Zero
      rw [SubSub.eq.Sub_Add]
      rw [AddSub.eq.Sub_Sub]
      rw [EqSubAdd.left]
      by_cases h_d' : d > 0
      ·
        apply MulSubS.le.Zero.of.In_Icc
        apply FMod.in.IccSign.of.FMod.ne.Zero.Gt_0 h_d' h_nd
      ·
        have h_d' := Le.of.NotGt h_d'
        have h_d' := Lt.of.Le.Ne h_d h_d'
        rw [Mul.comm]
        apply MulSubS.le.Zero.of.In_Icc
        apply FMod.in.Icc_Sign.of.FMod.ne.Zero.Lt_0 h_nd h_d'


-- created on 2025-03-30
