import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.InvDiv.eq.Div
import Lemma.Rat.MulDivS.eq.Div.of.Ne_0
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.StInv.eq.Inv.of.EqSt
import Lemma.Hyperreal.Infinitesimal0
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalSubDiv.Infinitesimal
open Hyperreal Rat Nat Int
export Hyperreal (Infinite Infinitesimal IsSt st)

/--
the approx operator that defines asymptotically equivalence/closeness between hyperreal numbers.
numerical analogy:
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
            apply Infinitesimal0
          .
            contrapose! h
            subst h
            apply Infinitesimal0
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
              simp [h_b] at h
              have := NotInfinitesimalSubDiv.of.NotInfinitesimal.Infinitesimal h_a h_b (d := 1)
              simp at this
              contradiction
        else
          simp [h_a] at ⊢ h
          if h_b : Infinitesimal b then
            simp [h_b] at h
          else
            simp [h_b] at h
            have h := EqSt.of.InfinitesimalSub h
            have h := StInv.eq.Inv.of.EqSt h
            rw [InvDiv.eq.Div] at h
            simp at h
            apply InfinitesimalSub.of.EqSt.NotInfinite _ h
            apply NotInfinite.of.NeSt_0
            linarith
      trans {a b c} h_ab h_bc:= by
        if h_a : Infinitesimal a then
          simp [h_a] at ⊢ h_ab
          if h_b : Infinitesimal b then
            simp [h_b] at ⊢ h_ab h_bc
            if h_c : Infinitesimal c then
              simp [h_c]
            else
              simp [h_c] at h_bc
              have := NotInfinitesimalSubDiv.of.NotInfinitesimal.Infinitesimal h_b h_c (d := 1)
              simp at this
              contradiction
          else
            simp [h_b] at h_ab
            have := NotInfinitesimalSubDiv.of.NotInfinitesimal.Infinitesimal h_a h_b (d := 1)
            simp at this
            contradiction
        else
          simp [h_a] at ⊢ h_ab
          if h_b : Infinitesimal b then
            simp [h_b] at h_ab
          else
            simp [h_b] at ⊢ h_ab h_bc
            if h_c : Infinitesimal c then
              simp [h_c] at h_bc
            else
              simp [h_c] at ⊢ h_bc
              have h_ab := EqSt.of.InfinitesimalSub h_ab
              have h_bc := EqSt.of.InfinitesimalSub h_bc
              have h_abc := Hyperreal.st_mul
                (x := a / b)
                (y := b / c)
                (NotInfinite.of.NeSt_0 (by linarith))
                (NotInfinite.of.NeSt_0 (by linarith))
              rw [MulDivS.eq.Div.of.Ne_0] at h_abc
              .
                apply InfinitesimalSub.of.EqSt.NotInfinite
                .
                  apply NotInfinite.of.NeSt_0
                  simp_all
                .
                  simp_all
              .
                contrapose! h_b
                subst h_b
                apply Infinitesimal0
    }

noncomputable instance : Coe ℝ ℝ* := ⟨Hyperreal.ofReal⟩

@[symm]
def HasEquiv.Equiv.symm [Setoid α] {a b : α} (h : a ≈ b) : b ≈ a := Setoid.symm h

def HasEquiv.Equiv.trans [Setoid α] {a b c : α} (h_ab : a ≈ b) (h_bc : b ≈ c) : a ≈ c := Setoid.trans h_ab h_bc

notation "∞" => Hyperreal.omega
