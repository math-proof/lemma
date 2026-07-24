import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.InvDiv.eq.Div
import Lemma.Rat.MulDivS.eq.Div.of.Ne_0
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.StInv.eq.Inv.of.EqSt
import Lemma.Hyperreal.Infinitesimal0
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalSubDiv.Infinitesimal
import Lemma.Nat.NotLt.is.Ge
open Hyperreal Rat Nat Int
export Hyperreal (Infinite Infinitesimal IsSt st)

abbrev XEq (α : Sort u) := Setoid α

namespace XEq
export Setoid (symm trans)
end XEq

/--
the approx operator that defines asymptotically equivalence/closeness between hyperreal numbers.
numerical analogy:
- [math.isclose][https://docs.python.org/3/library/math.html#math.isclose]
- [numpy.isclose][https://numpy.org/doc/stable/reference/generated/numpy.isclose.html]
-/
instance : XEq ℝ* where
  r a b := (a → 0) ∧ b → 0 ∨ (a / b - 1) → 0 ∧ ¬b → 0
  iseqv :=
    { refl x := by
        simp
        if h : x → 0 then
          simp [h]
        else
          simp [h]
          rw [Div.eq.One.of.Ne_0]
          .
            simp
            aesop
          .
            contrapose! h
            subst h
            apply Infinitesimal0
      symm {a b} h := by
        if h_a : a → 0 then
          simp [h_a] at ⊢ h
          if h_b : b → 0 then
            simp [h_b]
          else
            obtain h | h := h
            ·
              assumption
            ·
              have := NotInfinitesimalSubDiv.of.NotInfinitesimal.Infinitesimal h_a h_b (d := 1)
              aesop
        else
          simp [h_a] at ⊢ h
          if h_b : b → 0 then
            grind
          else
            have h := EqSt.of.InfinitesimalSub h.left
            have h := StInv.eq.Inv.of.EqSt h
            rw [InvDiv.eq.Div] at h
            simp at h
            apply InfinitesimalSub.of.EqSt.NotInfinite _ h
            apply NotInfinite.of.NeSt_0
            linarith
      trans {a b c} h_ab h_bc:= by
        if h_a : a → 0 then
          simp [h_a] at ⊢ h_ab
          if h_b : b → 0 then
            simp [h_b] at ⊢ h_ab h_bc
            if h_c : c → 0 then
              simp [h_c]
            else
              have := NotInfinitesimalSubDiv.of.NotInfinitesimal.Infinitesimal h_b h_c (d := 1)
              aesop
          else
            have := NotInfinitesimalSubDiv.of.NotInfinitesimal.Infinitesimal h_a h_b (d := 1)
            aesop
        else
          simp [h_a] at ⊢ h_ab
          if h_b : b → 0 then
            grind
          else
            simp [h_b] at ⊢ h_ab h_bc
            if h_c : c → 0 then
              grind
            else
              have h_ab := EqSt.of.InfinitesimalSub h_ab.left
              have h_bc := EqSt.of.InfinitesimalSub h_bc.left
              have h_abc := ArchimedeanClass.stdPart_mul
                (x := a / b)
                (y := b / c)
                (Ge.of.NotLt (NotInfinite.of.NeSt_0 (by linarith)))
                (Ge.of.NotLt (NotInfinite.of.NeSt_0 (by linarith)))
              rw [MulDivS.eq.Div.of.Ne_0] at h_abc
              .
                constructor
                .
                  apply InfinitesimalSub.of.EqSt.NotInfinite
                  .
                    apply NotInfinite.of.NeSt_0
                    simp_all
                  .
                    simp_all
                .
                  grind
              .
                contrapose! h_b
                subst h_b
                apply Infinitesimal0
    }

noncomputable instance : Coe ℝ ℝ* := ⟨Hyperreal.ofReal⟩

@[symm]
def HasEquiv.Equiv.symm [XEq α] {a b : α} (h : a ≈ b) : b ≈ a := XEq.symm h

def HasEquiv.Equiv.trans [XEq α] {a b c : α} (h_ab : a ≈ b) (h_bc : b ≈ c) : a ≈ c := XEq.trans h_ab h_bc

def Not.XEq.symm [XEq α] {a b : α} (h : ¬a ≈ b) : ¬b ≈ a := fun h' => h h'.symm

notation "∞" => Hyperreal.omega
