/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/MoritaGamma.lean -/


import Def.NumberTheory.Padics.MoritaGamma
import Lemma.Nat.Padics.MoritaGamma


example (p n : ℕ) [Fact p.Prime] :
    MetaMathlibExt.moritaGammaNat p n =
      (-1 : PadicInt p) ^ n *
        ∏ k ∈ (Finset.range n).filter (fun k => ¬p ∣ k), (k : PadicInt p) :=
  rfl

example (p : ℕ) [Fact p.Prime] :
    MetaMathlibExt.moritaGammaNat p 0 = 1 :=
  MetaMathlibExt.moritaGammaNat_zero p

example : MetaMathlibExt.moritaGammaNat 3 3 = (-2 : PadicInt 3) := by
  have h : (Finset.range 3).filter (fun k => ¬3 ∣ k) = {1, 2} := by
    decide
  calc
    MetaMathlibExt.moritaGammaNat 3 3 = (-1 : PadicInt 3) ^ 3 * 2 := by
      simp [MetaMathlibExt.moritaGammaNat, h]
    _ = -2 := by norm_num

example : MetaMathlibExt.moritaGammaNat 3 5 = (-8 : PadicInt 3) := by
  have h : (Finset.range 5).filter (fun k => ¬3 ∣ k) = {1, 2, 4} := by
    decide
  calc
    MetaMathlibExt.moritaGammaNat 3 5 = (-1 : PadicInt 3) ^ 5 * (2 * 4) := by
      simp [MetaMathlibExt.moritaGammaNat, h]
    _ = (-1 : PadicInt 3) ^ 5 * 8 := by norm_num
    _ = -8 := by norm_num

example {p : ℕ} [Fact p.Prime] {Γ : C(PadicInt p, PadicInt p)}
    (hΓ : MetaMathlibExt.IsMoritaPadicGamma p Γ) {n : ℕ} (hn : 0 < n) :
    Γ (n : PadicInt p) = MetaMathlibExt.moritaGammaNat p n :=
  hΓ.natCast_eq hn

example {p : ℕ} [Fact p.Prime] {Γ : C(PadicInt p, PadicInt p)}
    (hΓ : MetaMathlibExt.IsMoritaPadicGamma p Γ) : Γ 0 = 1 :=
  hΓ.zero_eq

example {p : ℕ} [Fact p.Prime] {Γ : C(PadicInt p, PadicInt p)}
    (hΓ : MetaMathlibExt.IsMoritaPadicGamma p Γ) (x : PadicInt p) :
    IsUnit (Γ x) :=
  hΓ.isUnit x

