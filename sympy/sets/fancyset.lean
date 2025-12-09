import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.InvDiv.eq.Inv
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.NotInfinite.of.NeSt_0
import Lemma.Hyperreal.StInv.eq.Inv.of.EqSt
import Lemma.Hyperreal.Infinitesimal_0
open Hyperreal Rat Nat Int
export Hyperreal (Infinite Infinitesimal IsSt st)


/--
the approx operator that defines asymptotically equivalence/closeness between hyperreal numbers.
numerical analogy:
- [torch.isclose](https://docs.pytorch.org/docs/stable/generated/torch.isclose.html)
- [math.isclose][https://docs.python.org/3/library/math.html#math.isclose]
- [numpy.isclose][https://numpy.org/doc/stable/reference/generated/numpy.isclose.html]
-/
instance : Setoid ℝ* where
  r a b := Infinitesimal a ∧ Infinitesimal b ∨ Infinitesimal (a / b - 1) ∧ ¬Infinitesimal b
  iseqv :=
    { refl x := by
        simp
        if h : x.Infinitesimal then
          simp [h]
        else
          simp [h]
          rw [Div.eq.One.of.Ne_0]
          .
            simp
            apply Infinitesimal_0
          .
            contrapose! h
            subst h
            apply Infinitesimal_0
      symm {a b} h := by
        if h_a : Infinitesimal a then
          simp [h_a] at ⊢ h
          if h_b : Infinitesimal b then
            simp [h_b]
          else
            obtain h | h := h
            ·
              assumption
            ·
              have h := EqSt.of.InfinitesimalSub h.1
              have h_ab := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a h_b
              have h_ab := EqSt_0.of.Infinitesimal h_ab
              rw [h_ab] at h
              simp at h
        else
          simp [h_a] at ⊢ h
          if h_b : Infinitesimal b then
            simp [h_b] at h
          else
            have h := h.1
            have h := EqSt.of.InfinitesimalSub h
            have h := StInv.eq.Inv.of.EqSt h
            rw [InvDiv.eq.Inv] at h
            simp at h
            apply InfinitesimalSub.of.EqSt.NotInfinite _ h
            apply NotInfinite.of.NeSt_0
            linarith
      trans {x y z} h₀ h₁:= by
        sorry
    }
