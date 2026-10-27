import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicElliptic
open PadicElliptic
open scoped Padic


namespace PadicElliptic

/--
[inPadicFiltration_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean)
-/
@[path]
lemma inPadicFiltration_mono
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {W : WeierstrassCurve ℚ}
  {n : ℕ}
  {P : PadicPointGroup W (p := p)}
-- given
  (h : InPadicFiltration W (n + 1) P) :
-- imply
  InPadicFiltration W n P := by
-- proof
  match P with
  | .zero => exact trivial
  | .some x y h' =>
    simp only [InPadicFiltration] at h ⊢
    exact ⟨h.1, le_trans (by omega) h.2⟩

end PadicElliptic

namespace PadicElliptic

/--
[negY_short_weierstrass](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean)
-/
@[path]
lemma negY_short_weierstrass
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {W : WeierstrassCurve ℚ}
  {x y : ℚ_[p]}
-- given
  (ha1 : W.a₁ = 0)
  (ha3 : W.a₃ = 0) :
-- imply
  (W.baseChange ℚ_[p]).toAffine.negY x y = -y := by
-- proof
  unfold WeierstrassCurve.baseChange WeierstrassCurve.toAffine WeierstrassCurve.Affine.negY
  simp [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, ha1, ha3]

end PadicElliptic

namespace PadicElliptic

/--
[negation_preserves_filtration](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean)
-/
@[path]
lemma negation_preserves_filtration
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {W : WeierstrassCurve ℚ}
  {n : ℕ}
-- given
  (ha1 : W.a₁ = 0)
  (ha3 : W.a₃ = 0)
  (P : PadicPointGroup W (p := p)) :
-- imply
  InPadicFiltration W n P → InPadicFiltration W n (-P) := by
-- proof
  match P with
  | .zero =>
    intro _
    show InPadicFiltration W n (-(0 : PadicPointGroup W))
    rw [neg_zero]
    trivial
  | .some x y h =>
    intro ⟨hy, hval⟩
    rw [WeierstrassCurve.Affine.Point.neg_some]
    have hNegY : (W.baseChange ℚ_[p]).toAffine.negY x y = -y :=
      negY_short_weierstrass W ha1 ha3 x y
    show (W.baseChange ℚ_[p]).toAffine.negY x y ≠ 0 ∧
      (n : ℤ) ≤ Padic.valuation x -
        Padic.valuation ((W.baseChange ℚ_[p]).toAffine.negY x y)
    rw [hNegY]
    exact ⟨neg_ne_zero.mpr hy, by rw [padic_valuation_neg]; exact hval⟩

end PadicElliptic

namespace PadicElliptic

/--
[index_eq_p_of_surjective_hom_to_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean)
-/
@[path]
lemma index_eq_p_of_surjective_hom_to_zmod
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  [AddGroup G]
  {H : AddSubgroup G}
  {f : G →+ ZMod p}
-- given
  (hf : Function.Surjective f)
  (hker : f.ker = H) :
-- imply
  H.index = p := by
-- proof
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    AddSubgroup.card_top, Nat.card_eq_fintype_card, ZMod.card]

end PadicElliptic

namespace PadicElliptic

/--
[inPadicFiltration_all_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean)
-/
@[path]
lemma inPadicFiltration_all_eq_zero
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {W : WeierstrassCurve ℚ}
  {P : PadicPointGroup W (p := p)}
-- given
  (h : ∀ n : ℕ, InPadicFiltration W n P) :
-- imply
  P = 0 := by
-- proof
  match P with
  | .zero => rfl
  | .some x y hns =>
    exfalso
    have : ∀ n : ℕ, (n : ℤ) ≤ Padic.valuation x - Padic.valuation y := fun n => (h n).2
    have := this (Int.toNat (Padic.valuation x - Padic.valuation y) + 1)
    omega
/-- Axiomatized: if $P \in E_n(\mathbb{Q}_p)$ and $pP = 0$, then $P$ already lies in
$E_{n+1}(\mathbb{Q}_p)$. -/
end PadicElliptic


/--
[padic_valuation_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean)
-/
@[path]
private lemma padic_valuation_neg_eq
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {y : ℚ_[p]} :
-- imply
  (-y).valuation = y.valuation := by
-- proof
  apply PadicElliptic.padic_valuation_neg y


-- created on 2026-10-23
