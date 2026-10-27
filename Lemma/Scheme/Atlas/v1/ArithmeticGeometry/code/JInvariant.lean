import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
open WeierstrassCurve shortWeierstrassCurve


namespace shortWeierstrassCurve

variable [CommRing R] (a₄ a₆ : R)
/--
[c₄_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma c₄_eq : (shortWeierstrassCurve a₄ a₆).c₄ = -48 * a₄ := by
  simp only [shortWeierstrassCurve, c₄, b₂, b₄]; ring

end shortWeierstrassCurve

namespace shortWeierstrassCurve

variable [CommRing R] (a₄ a₆ : R)
/--
[c₆_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma c₆_eq : (shortWeierstrassCurve a₄ a₆).c₆ = -864 * a₆ := by
  simp only [shortWeierstrassCurve, c₆, b₂, b₄, b₆]; ring

end shortWeierstrassCurve

namespace shortWeierstrassCurve

variable [CommRing R] (a₄ a₆ : R)
/--
[Δ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
$\Delta = -16(4 a_4^3 + 27 a_6^2)$. -/
lemma Δ_eq : (shortWeierstrassCurve a₄ a₆).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
  simp only [shortWeierstrassCurve, Δ, b₂, b₄, b₆, b₈]; ring

end shortWeierstrassCurve

/--
[j_mul_Δ_eq_c₄_cube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
elliptic Weierstrass curve. -/
lemma WeierstrassCurve.j_mul_Δ_eq_c₄_cube {R : Type*} [CommRing R]
  (W : WeierstrassCurve R) [W.IsElliptic] :
  W.j * W.Δ = W.c₄ ^ 3 := by
  simp only [j]
  have h : (↑W.Δ'⁻¹ : R) * W.Δ = 1 := Units.inv_mul W.Δ'
  calc ↑W.Δ'⁻¹ * W.c₄ ^ 3 * W.Δ
    = W.c₄ ^ 3 * (↑W.Δ'⁻¹ * W.Δ) := by ring
    _ = W.c₄ ^ 3 * 1 := by rw [h]
    _ = W.c₄ ^ 3 := mul_one _
section JInvariantFormula
variable {F : Type*} [Field F]

/--
[shortWeierstrassCurve.sixteen_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma shortWeierstrassCurve.sixteen_ne_zero
  [Field F]
  {a₄ a₆ : F}
  [(shortWeierstrassCurve a₄ a₆).IsElliptic] :
-- imply
  (16 : F) ≠ 0 := by
-- proof
  intro h16
  exact (shortWeierstrassCurve a₄ a₆).isUnit_Δ.ne_zero (by
    rw [shortWeierstrassCurve.Δ_eq]
    rw [show (-16 : F) = -(16 : F) from by norm_num, h16, neg_zero, zero_mul])

/--
[shortWeierstrassCurve.denominator_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma shortWeierstrassCurve.denominator_ne_zero
  [Field F]
  {a₄ a₆ : F}
  [(shortWeierstrassCurve a₄ a₆).IsElliptic] :
-- imply
  4 * a₄ ^ 3 + 27 * a₆ ^ 2 ≠ 0 := by
-- proof
  intro heq
  exact (shortWeierstrassCurve a₄ a₆).isUnit_Δ.ne_zero (by
    rw [shortWeierstrassCurve.Δ_eq, heq, mul_zero])

/--
[j_invariant_short_weierstrass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma j_invariant_short_weierstrass_eq
  [Field F]
  {a₄ a₆ : F}
  [(shortWeierstrassCurve a₄ a₆).IsElliptic] :
-- imply
  (shortWeierstrassCurve a₄ a₆).j = 1728 * (4 * a₄ ^ 3) / (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
-- proof
  rw [eq_div_iff (shortWeierstrassCurve.denominator_ne_zero a₄ a₆)]
  have h_jΔ := WeierstrassCurve.j_mul_Δ_eq_c₄_cube (shortWeierstrassCurve a₄ a₆)
  rw [shortWeierstrassCurve.Δ_eq, shortWeierstrassCurve.c₄_eq] at h_jΔ
  apply mul_left_cancel₀
    (neg_ne_zero.mpr (shortWeierstrassCurve.sixteen_ne_zero a₄ a₆) : (-16 : F) ≠ 0)
  linear_combination h_jΔ
end JInvariantFormula

/--
[ellipticCurveOfJ_jInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma ellipticCurveOfJ_jInvariant
  [Field k]
  {j : k} :
-- imply
  (ellipticCurveOfJ j).jInvariant = j :=
-- proof
  (j_invariant_surjective j).choose_spec

/--
[j_invariant_surjective_fun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma j_invariant_surjective_fun
  [Field k] :
-- imply
  Function.Surjective (EllipticCurveOver.jInvariant (k := k)) :=
-- proof
  j_invariant_surjective
section Jacobian
variable {k : Type*} [Field k]

/--
[EllipticCurveOver.RationalPoints_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma EllipticCurveOver.RationalPoints_def
  [Field k]
  {E : EllipticCurveOver k} :
-- imply
  E.RationalPoints = E.curve.toAffine.Point :=
-- proof
  rfl
/-- The Mordell–Weil abelian group structure on $E(k)$. -/
end Jacobian
/-- The canonical isomorphism $\mathrm{Pic}^0(C) \cong J(C)(k)$ identifying the
degree-zero Picard group of a genus-one curve with the $k$-rational points of
its Jacobian. -/
variable {k : Type u} [Field k] [NumberField k]

/--
[TateShafarevich.range_eq_ker_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma TateShafarevich.range_eq_ker_axiom
  {k : Type u}
  [Field k]
  [NumberField k]
  {k : Type u}
  [Field k]
  [NumberField k]
  {E : EllipticCurveOver k} :
-- imply
  (TateShafarevich.toWC E).range = TateShafarevich.asKernel E := by
-- proof
  rw [TateShafarevich.toWC, AddSubgroup.subtype_range]
  ext x
  constructor
  · intro hx
    rw [TateShafarevich.asKernel, AddMonoidHom.mem_ker]
    simp only [WeilChateletGroup.localizationMap, WeilChateletGroup.localizationMapAxiom]
    funext v
    simp only [AddMonoidHom.mk'_apply]
    exact (TateShafarevich.mem_iff E x).mp hx v
  · intro hx
    rw [TateShafarevich.asKernel, AddMonoidHom.mem_ker] at hx
    rw [TateShafarevich.mem_iff]
    intro v
    have hv : (WeilChateletGroup.localizationMapAxiom E x) v = (0 : LocalWCProduct E) v := by
      rw [show WeilChateletGroup.localizationMapAxiom E x = (0 : LocalWCProduct E) from by
        change (WeilChateletGroup.localizationMap E) x = 0; exact hx]
    simp only [WeilChateletGroup.localizationMapAxiom, AddMonoidHom.mk'_apply] at hv
    exact hv

/--
[TateShafarevich.range_eq_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma TateShafarevich.range_eq_ker
  {k : Type u}
  [Field k]
  [NumberField k]
  {E : EllipticCurveOver k} :
-- imply
  (TateShafarevich.toWC E).range = TateShafarevich.asKernel E :=
-- proof
  TateShafarevich.range_eq_ker_axiom E

/--
[mem_tateShafarevich_asKernel_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma mem_tateShafarevich_asKernel_iff
  {k : Type u}
  [Field k]
  [NumberField k]
  {E : EllipticCurveOver k}
  {x : WeilChateletGroup E} :
-- imply
  x ∈ TateShafarevich.asKernel E ↔ WeilChateletGroup.localizationMap E x = 0 :=
-- proof
  Iff.rfl

/--
[GenusOneCurve.PointOverAlgClosure.nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma GenusOneCurve.PointOverAlgClosure.nonempty
  {k : Type u}
  [Field k]
  [NumberField k]
  {k : Type u}
  [Field k]
  {C : GenusOneCurve k} :
-- imply
  Nonempty (C.PointOverAlgClosure) :=
-- proof
  ⟨(0 : (C.Jacobian.curve.baseChange (AlgebraicClosure k)).toAffine.Point)⟩

/--
[GenusOneCurve.translationIsomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma GenusOneCurve.translationIsomorphism
  {k : Type u}
  [Field k]
  [NumberField k]
  {k : Type u}
  [Field k]
  {C : GenusOneCurve k}
  {O O' : C.PointOverAlgClosure} :
-- imply
  ∃ σ : WeierstrassCurve.VariableChange (AlgebraicClosure k), (C.ellipticCurveAtBasePoint O').curve = σ • (C.ellipticCurveAtBasePoint O).curve :=
-- proof
  ⟨C.weierstrassModel O' * (C.weierstrassModel O)⁻¹,
    by simp only [ellipticCurveAtBasePoint, mul_smul, inv_smul_smul]⟩

/--
[GenusOneCurve.jInvariant_eq_of_basePoints](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma GenusOneCurve.jInvariant_eq_of_basePoints
  {k : Type u}
  [Field k]
  [NumberField k]
  {k : Type u}
  [Field k]
  {C : GenusOneCurve k}
  {O O' : C.PointOverAlgClosure} :
-- imply
  (C.ellipticCurveAtBasePoint O).jInvariant = (C.ellipticCurveAtBasePoint O').jInvariant := by
-- proof
  simp only [EllipticCurveOver.jInvariant, ellipticCurveAtBasePoint, variableChange_j]

/--
[GenusOneCurve.jInvariant_eq_jacobian_jInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma GenusOneCurve.jInvariant_eq_jacobian_jInvariant
  {k : Type u}
  [Field k]
  [NumberField k]
  {k : Type u}
  [Field k]
  {C : GenusOneCurve k} :
-- imply
  C.jInvariant = C.Jacobian.jInvariant :=
-- proof
  rfl

/--
[j_eq_of_isomorphic_over_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma j_eq_of_isomorphic_over_closure
  {k : Type u}
  [Field k]
  [NumberField k]
  [Field k]
  {W₁ W₂ : WeierstrassCurve k}
  [W₁.IsElliptic]
  [W₂.IsElliptic]
-- given
  (h : ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure k)), C • (W₁.baseChange (AlgebraicClosure k)) = W₂.baseChange (AlgebraicClosure k)) :
-- imply
  W₁.j = W₂.j := by
-- proof
  obtain ⟨C, hC⟩ := h
  have h1 := W₁.map_j (algebraMap k (AlgebraicClosure k))
  have h2 := W₂.map_j (algebraMap k (AlgebraicClosure k))
  have h3 := variableChange_j (W₁.baseChange (AlgebraicClosure k)) C
  have h4 : (C • W₁.baseChange (AlgebraicClosure k)).j =
    (W₂.baseChange (AlgebraicClosure k)).j := by simp only [hC]
  have h5 : (W₁.baseChange (AlgebraicClosure k)).j =
    (W₂.baseChange (AlgebraicClosure k)).j := h3.symm.trans h4
  change (W₁.map (algebraMap k (AlgebraicClosure k))).j =
    (W₂.map (algebraMap k (AlgebraicClosure k))).j at h5
  rw [h1, h2] at h5
  exact (algebraMap k (AlgebraicClosure k)).injective h5

/--
[isomorphic_over_closure_of_j_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma isomorphic_over_closure_of_j_eq
  {k : Type u}
  [Field k]
  [NumberField k]
  [Field k]
  {W₁ W₂ : WeierstrassCurve k}
  [W₁.IsElliptic]
  [W₂.IsElliptic]
-- given
  (hj : W₁.j = W₂.j) :
-- imply
  ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure k)), C • (W₁.baseChange (AlgebraicClosure k)) = W₂.baseChange (AlgebraicClosure k) := by
-- proof
  have h1 := W₁.map_j (algebraMap k (AlgebraicClosure k))
  have h2 := W₂.map_j (algebraMap k (AlgebraicClosure k))
  have hj' : (W₁.baseChange (AlgebraicClosure k)).j =
    (W₂.baseChange (AlgebraicClosure k)).j := by
    change (W₁.map (algebraMap k (AlgebraicClosure k))).j =
      (W₂.map (algebraMap k (AlgebraicClosure k))).j
    rw [h1, h2, hj]
  exact exists_variableChange_of_j_eq _ _ hj'

/--
[j_invariant_iff_isomorphic_over_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
lemma j_invariant_iff_isomorphic_over_closure
  {k : Type u}
  [Field k]
  [NumberField k]
  [Field k]
  {W₁ W₂ : WeierstrassCurve k}
  [W₁.IsElliptic]
  [W₂.IsElliptic] :
-- imply
  W₁.j = W₂.j ↔ ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure k)), C • (W₁.baseChange (AlgebraicClosure k)) = W₂.baseChange (AlgebraicClosure k) :=
-- proof
  ⟨isomorphic_over_closure_of_j_eq W₁ W₂, j_eq_of_isomorphic_over_closure W₁ W₂⟩

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma a_eq
  [CommRing R]
  {a₄ a₆ : R} :
-- imply
  (shortWeierstrassCurve a₄ a₆).a₁ = 0 := by
-- proof
  apply shortWeierstrassCurve.a a₄ a₆

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma a_eq_2
  [CommRing R]
  {a₄ a₆ : R} :
-- imply
  (shortWeierstrassCurve a₄ a₆).a₂ = 0 := by
-- proof
  apply shortWeierstrassCurve.a a₄ a₆

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma a_eq_3
  [CommRing R]
  {a₄ a₆ : R} :
-- imply
  (shortWeierstrassCurve a₄ a₆).a₃ = 0 := by
-- proof
  apply shortWeierstrassCurve.a a₄ a₆

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma a_eq_4
  [CommRing R]
  {a₄ a₆ : R} :
-- imply
  (shortWeierstrassCurve a₄ a₆).a₄ = a₄ := by
-- proof
  apply shortWeierstrassCurve.a a₄ a₆

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma a_eq_5
  [CommRing R]
  {a₄ a₆ : R} :
-- imply
  (shortWeierstrassCurve a₄ a₆).a₆ = a₆ := by
-- proof
  apply shortWeierstrassCurve.a a₄ a₆

/--
[c](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma c_eq
  [CommRing R]
  {a₄ a₆ : R} :
-- imply
  (shortWeierstrassCurve a₄ a₆).c₄ = -48 * a₄ := by
-- proof
  apply shortWeierstrassCurve.c a₄ a₆

/--
[c](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma c_eq_2
  [CommRing R]
  {a₄ a₆ : R} :
-- imply
  (shortWeierstrassCurve a₄ a₆).c₆ = -864 * a₆ := by
-- proof
  apply shortWeierstrassCurve.c a₄ a₆

/--
[WeierstrassCurve.j_mul_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma j_mul__eq
  [CommRing R]
  {W : WeierstrassCurve R}
  [W.IsElliptic] :
-- imply
  W.j * W.Δ = W.c₄ ^ 3 := by
-- proof
  apply WeierstrassCurve.j_mul_ W

/--
[j_invariant_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean)
-/
@[path]
private lemma j_invariant_surjective_eq
  [Field k]
  {j : k} :
-- imply
  ∃ E : EllipticCurveOver k, E.jInvariant = j := by
-- proof
  apply j_invariant_surjective j


-- created on 2026-10-23
