import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.EqSt_0.of.NotInfinitesimal.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.InfiniteMul.of.Infinite.NotInfinitesimal
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfiniteDiv.of.StAddDivS.ne.Zero
import Lemma.Hyperreal.NotInfiniteInv.of.Infinite
import Lemma.Hyperreal.StAdd.eq.AddSt.of.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Nat.Add
import Lemma.Rat.Div_AddAddSquareS.eq.Div_Add_AddDivS.of.Ne_0.Ne_0
import Lemma.Rat.EqDiv.is.Eq_Div.of.Ne_0
import Lemma.Real.Eq_1.of.Add_Inv.eq.Two
open Hyperreal Nat Rat Real


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b)
  (h_a_inf : Infinite a)
  (h : ((2 * a * b + 1) / (a² + b² + 1)).st = 1) :
-- imply
  (a / b).st = 1 := by
-- proof
  have h_a_ne_0 := Ne_0.of.NotInfinitesimal h_a
  have h_b_ne_0 := Ne_0.of.NotInfinitesimal h_b
  rw [Div_AddAddSquareS.eq.Div_Add_AddDivS.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0] at h
  have h_ab := InfiniteMul.of.Infinite.NotInfinitesimal h_a_inf h_b
  have h_ab := InfinitesimalInv.of.Infinite h_ab
  have h_eq_add_st : st ((a * b)⁻¹ + 2) = 2 := by
    rw [show (2 : ℝ*) = (2 : ℝ) by rfl]
    rw [StAdd.eq.AddSt.of.NotInfinite]
    ·
      rw [EqSt_0.of.Infinitesimal h_ab]
      simp
    ·
      apply NotInfinite.of.Infinitesimal h_ab
  rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal] at h
  ·
    rw [h_eq_add_st] at h
    have h := Eq_Div.of.EqDiv.Ne_0 (by simp) (y := 2) h
    conv_rhs at h => simp
    rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite] at h
    ·
      have h_eq_add_st : ((a * b)⁻¹ + (2 : ℝ)).st = 2 := by
        assumption
      rw [StAdd.eq.AddSt.of.NotInfinite] at h_eq_add_st
      ·
        rw [← h_eq_add_st] at h
        simp at h
        rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite] at h
        ·
          rw [StDiv.eq.InvStInv (a := b)] at h
          apply Eq_1.of.Add_Inv.eq.Two h
        ·
          apply NotInfiniteDiv.of.StAddDivS.ne.Zero
          linarith
        ·
          rw [Add.comm] at h
          apply NotInfiniteDiv.of.StAddDivS.ne.Zero
          linarith
      ·
        apply NotInfiniteInv.of.Infinite
        assumption
    ·
      apply NotInfiniteInv.of.Infinite
      assumption
    ·
      by_contra h_inf
      have h_inf := InfiniteAdd.of.Infinite.NotInfinite (NotInfinite.of.Infinitesimal h_ab) h_inf
      have := EqSt_0.of.Infinite h_inf
      linarith
  ·
    apply NotInfiniteAdd.of.NotInfinite
    apply NotInfinite.of.Infinitesimal h_ab
  ·
    by_contra h_eps
    have h_ne_eps := NotInfinitesimal.of.NeSt_0 (by linarith)
    linarith [EqSt_0.of.NotInfinitesimal.Infinitesimal h_ne_eps h_eps]


-- created on 2025-12-20
