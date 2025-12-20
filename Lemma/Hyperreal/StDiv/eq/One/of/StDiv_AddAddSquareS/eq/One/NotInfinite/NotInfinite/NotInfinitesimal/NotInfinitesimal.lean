import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.NotInfinitesimalAdd.of.NotInfinitesimal.NotInfinitesimal.Le0Mul
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Nat.Le0Add.of.Ge_0.Ge_0
import Lemma.Nat.Mul
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Nat.Square.eq.Mul
import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.Div_AddAddSquareS.eq.Div_Add_AddDivS.of.Ne_0.Ne_0
import Lemma.Rat.Div_Mul.eq.Div1.of.Ne_0
import Lemma.Rat.EqDiv.is.Eq_Div.of.Ne_0
import Lemma.Rat.EqDiv_1
import Lemma.Rat.GeInvSquare_0
import Lemma.Rat.MulDivS.eq.DivMulS
import Lemma.Rat.MulDivS.eq.One.of.Ne_0.Ne_0
import Lemma.Real.Eq_1.of.Add_Inv.eq.Two
open Hyperreal Nat Rat Real


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b)
  (h_a_inf : ¬Infinite a)
  (h_b_inf : ¬Infinite b)
  (h : ((2 * a * b + 1) / (a² + b² + 1)).st = 1) :
-- imply
  (a / b).st = 1 := by
-- proof
  have h_a_ne_0 := Ne_0.of.NotInfinitesimal h_a
  have h_b_ne_0 := Ne_0.of.NotInfinitesimal h_b
  rw [Div_AddAddSquareS.eq.Div_Add_AddDivS.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0] at h
  have h_ab_inf := NotInfiniteMul.of.NotInfinite.NotInfinite h_a_inf h_b_inf
  have h_ab_eps := NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a h_b
  have h_eq_st_add_inv : st ((a * b)⁻¹ + 2) = st (a * b)⁻¹ + 2 := by
    rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
    ·
      simp
      apply EqSt
    ·
      apply NotInfiniteInv.of.NotInfinitesimal h_ab_eps
    ·
      apply NotInfinite
  have h_inf_div_ab := NotInfiniteDiv.of.NotInfinite.NotInfinitesimal h_b h_a_inf
  have h_inf_div_ba := NotInfiniteDiv.of.NotInfinite.NotInfinitesimal h_a h_b_inf
  have h_eq_st_add_inv' : st ((a * b)⁻¹ + (a / b + b / a)) = st (a * b)⁻¹ + st (a / b + b / a) := by
    rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
    ·
      apply NotInfiniteInv.of.NotInfinitesimal h_ab_eps
    ·
      apply NotInfiniteAdd.of.NotInfinite.NotInfinite h_inf_div_ab h_inf_div_ba
  rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal] at h
  ·
    rw [h_eq_st_add_inv, h_eq_st_add_inv'] at h
    have h_add_st_ne_0 : (a * b)⁻¹.st + 2 ≠ 0 := by
      by_contra h_add_st_ne_0
      rw [h_add_st_ne_0] at h
      simp at h
    have h := Eq_Div.of.EqDiv.Ne_0 h_add_st_ne_0 h
    rw [EqDiv_1] at h
    simp at h
    rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_inf_div_ab h_inf_div_ba] at h
    rw [StDiv.eq.InvStInv (a := b)] at h
    apply Eq_1.of.Add_Inv.eq.Two h
  ·
    apply NotInfiniteAdd.of.NotInfinite
    apply NotInfiniteInv.of.NotInfinitesimal h_ab_eps
  ·
    apply NotInfinitesimalAdd.of.NotInfinitesimal.NotInfinitesimal.Le0Mul
    ·
      rw [Inv.eq.Div1]
      rw [Mul_Add.eq.AddMulS]
      repeat rw [MulDivS.eq.DivMulS]
      simp
      conv_rhs =>
        arg 2
        rw [Mul.comm (a := a) (b := b)]
      repeat rw [MulMul.eq.Mul_Mul]
      repeat rw [Div_Mul.eq.Div1.of.Ne_0 (by assumption)]
      simp [Mul.eq.Square]
      apply Le0Add.of.Ge_0.Ge_0
      repeat apply GeInvSquare_0
    ·
      have : NeZero (a * b) := ⟨Mul.ne.Zero.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0⟩
      apply NotInfinitesimalInv.of.NotInfinite h_ab_inf
    ·
      apply NotInfinitesimalAdd.of.NotInfinitesimal.NotInfinitesimal.Le0Mul
      ·
        simp [MulDivS.eq.One.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0]
      ·
        have : NeZero b := ⟨h_b_ne_0⟩
        apply NotInfinitesimalDiv.of.NotInfinite.NotInfinitesimal h_a h_b_inf
      ·
        have : NeZero a := ⟨h_a_ne_0⟩
        apply NotInfinitesimalDiv.of.NotInfinite.NotInfinitesimal h_b h_a_inf


-- created on 2025-12-20
