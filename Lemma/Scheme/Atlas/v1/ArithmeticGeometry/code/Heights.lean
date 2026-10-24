import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Heights
open Height MvPolynomial NumberField WeierstrassCurve AddSubgroup Filter Topology Polynomial Set AbsoluteHeight EllipticCurve EllipticCurve.WeakMordellWeil CanonicalHeight TateTheorem Northcott
open Height NumberField
open WeierstrassCurve AddSubgroup
open Filter Topology
open CanonicalHeight
open Height Polynomial Set
open AddSubgroup Set


namespace AbsoluteHeight

/--
[absoluteHeight_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma absoluteHeight_mk
  [Field K]
  [NumberField K]
  [Empty.Finite ι]
  {x : ι → K}
-- given
  (hx : x ≠ 0) :
-- imply
  absoluteHeight (Projectivization.mk K x hx) = Height.mulHeight x := by
-- proof
  simp [absoluteHeight, Projectivization.mulHeight_mk]

end AbsoluteHeight

namespace AbsoluteHeight

/--
[logHeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma logHeight_eq
  [Field K]
  [NumberField K]
  [Empty.Finite ι]
  {P : Projectivization K (ι → K)} :
-- imply
  logHeight P = Projectivization.logHeight P := by
-- proof
  simp [logHeight, absoluteHeight, Projectivization.logHeight_eq_log_mulHeight]
end AbsoluteHeight
section HeightProperties


/--
[weil_height_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma weil_height_ge_one
  [Field K]
  [NumberField K]
  {n : ℕ}
  {x : Fin (n + 1) → K} :
-- imply
  1 ≤ mulHeight x :=
-- proof
  one_le_mulHeight x
end HeightProperties
section Morphism
variable {K : Type*} [Field K] [NumberField K]
variable {n m d : ℕ}

/--
[height_morphism_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma height_morphism_upper_bound
  [Field K]
  [NumberField K]
  {n m d : ℕ}
  {φ : Fin (m + 1) → MvPolynomial (Fin (n + 1)) K}
-- given
  (hφ : ∀ i, (φ i).IsHomogeneous d) :
-- imply
  ∃ (c : ℝ), ∀ (x : Fin (n + 1) → K), logHeight (fun j => MvPolynomial.eval x (φ j)) ≤ (d : ℝ) * logHeight x + c := by
-- proof
  obtain ⟨C, hC⟩ := logHeight_eval_le' hφ
  exact ⟨C, fun x => by linarith [hC x]⟩
end Morphism
section Automorphism
variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/--
[height_automorphism_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma height_automorphism_bound
  [Field K]
  [NumberField K]
  {n : ℕ}
  {φ : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K}
  {ψ : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K}
-- given
  (hφ : ∀ i, (φ i).IsHomogeneous 1)
  (hψ : ∀ i, (ψ i).IsHomogeneous 1)
  (hinv : ∀ (x : Fin (n + 1) → K) (i : Fin (n + 1)), MvPolynomial.eval (fun j => MvPolynomial.eval x (φ j)) (ψ i) = x i) :
-- imply
  ∃ (c : ℝ), ∀ (x : Fin (n + 1) → K), |logHeight (fun j => MvPolynomial.eval x (φ j)) - logHeight x| ≤ c := by
-- proof
  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' hφ
  obtain ⟨C₂, hC₂⟩ := logHeight_eval_le' hψ
  refine ⟨max C₁ C₂, fun x => ?_⟩
  rw [abs_le]
  have hC₁x := hC₁ x
  have hC₂x := hC₂ (fun j => MvPolynomial.eval x (φ j))
  have heq : (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval x (φ j)) (ψ i)) = x := by
    ext i; exact hinv x i
  rw [heq] at hC₂x
  simp only [Nat.cast_one, one_mul] at hC₁x hC₂x
  constructor <;> linarith [le_max_left C₁ C₂, le_max_right C₁ C₂]
end Automorphism

/--
[galoisEquivFinitePlace_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma galoisEquivFinitePlace_apply
  [Field K]
  [NumberField K]
  {σ : K ≃ₐ[ℚ] K}
  {v : NumberField.FinitePlace K}
  {y : K} :
-- imply
  (galoisEquivFinitePlace σ v) y = v (σ.symm y) :=
-- proof
  rfl
noncomputable section
open Height NumberField
section GaloisInvariance
variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Empty.Finite ι]

/--
[prod_infinitePlace_galois_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma prod_infinitePlace_galois_eq
  [Field K]
  [NumberField K]
  [Empty.Finite ι]
  {σ : K ≃ₐ[ℚ] K}
  {x : ι → K} :
-- imply
  ∏ v : InfinitePlace K, (⨆ i, v (σ (x i))) ^ v.mult = ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
-- proof
  apply Fintype.prod_equiv (MulAction.toPerm σ⁻¹)
  intro v
  simp only [MulAction.toPerm_apply]
  have hval : ∀ i, v (σ (x i)) = (σ⁻¹ • v) (x i) := by
    intro i; rw [InfinitePlace.smul_apply]; congr 1
  simp_rw [hval]
  congr 1
  unfold InfinitePlace.mult
  rw [InfinitePlace.isReal_smul_iff]

/--
[finprod_finitePlace_galois_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma finprod_finitePlace_galois_eq
  [Field K]
  [NumberField K]
  [Empty.Finite ι]
  {σ : K ≃ₐ[ℚ] K}
  {x : ι → K} :
-- imply
  ∏ᶠ v : FinitePlace K, ⨆ i, v (σ (x i)) = ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
-- proof
  simp_rw [show ∀ (v : FinitePlace K) (i : ι), v (σ (x i)) =
    (galoisEquivFinitePlace σ⁻¹ v) (x i)
    from fun v i => by rw [galoisEquivFinitePlace_apply]; congr 1]
  exact finprod_comp_equiv (galoisEquivFinitePlace σ⁻¹) (f := fun v => ⨆ i, v (x i))

/--
[mulHeight_galois_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma mulHeight_galois_invariant
  [Field K]
  [NumberField K]
  [Empty.Finite ι]
  {σ : K ≃ₐ[ℚ] K}
  {x : ι → K} :
-- imply
  mulHeight (σ ∘ x) = mulHeight x := by
-- proof
  by_cases hx : x = 0
  · simp [hx]
  · have hσx : σ ∘ x ≠ 0 := by
    intro h; apply hx; funext i
    have := congr_fun h i
    simp [Function.comp] at this
    exact this
    rw [NumberField.mulHeight_eq hσx, NumberField.mulHeight_eq hx]
    simp only [Function.comp_apply]
    exact congr_arg₂ (· * ·)
      (prod_infinitePlace_galois_eq σ x) (finprod_finitePlace_galois_eq σ x)

/--
[logHeight_galois_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma logHeight_galois_invariant
  [Field K]
  [NumberField K]
  [Empty.Finite ι]
  {σ : K ≃ₐ[ℚ] K}
  {x : ι → K} :
-- imply
  logHeight (σ ∘ x) = logHeight x := by
-- proof
  simp only [logHeight, mulHeight_galois_invariant σ x]
end GaloisInvariance
end
open WeierstrassCurve AddSubgroup

namespace EllipticCurve.WeakMordellWeil

/--
[lemma_25_3_phi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma lemma_25_3_phi
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {data : TwoIsogenyData W} :
-- imply
  data.descentMap.ker = data.phi.range :=
-- proof
  data.descentMap_ker_eq

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[lemma_25_3_phi_hat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma lemma_25_3_phi_hat
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {data : TwoIsogenyData W} :
-- imply
  data.descentMap'.ker = data.phi_hat.range :=
-- proof
  data.descentMap'_ker_eq

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[square_class_self_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma square_class_self_add
  {g : ℚˣ ⧸ Subgroup.square ℚˣ} :
-- imply
  Additive.ofMul g + Additive.ofMul g = 0 := by
-- proof
  rw [← ofMul_mul, ofMul_eq_zero]
  induction g using Quotient.inductionOn' with
  | h g => exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[square_class_mk_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma square_class_mk_mul
  {x y : ℚ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0) :
-- imply
  QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (x * y) (mul_ne_zero hx hy)) = QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 x hx) * QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 y hy) := by
-- proof
  rw [← map_mul]; congr 1; ext; simp [Units.mk0]

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[square_class_mul_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma square_class_mul_eq_div
  {x y : ℚ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0) :
-- imply
  QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (x * y) (mul_ne_zero hx hy)) = QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (x / y) (div_ne_zero hx hy)) := by
-- proof
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_square, isSquare_iff_exists_sq]
  refine ⟨Units.mk0 (y⁻¹) (inv_ne_zero hy), ?_⟩
  ext
  show ((Units.mk0 (x * y) _)⁻¹ * (Units.mk0 (x / y) _)).val = ((Units.mk0 (y⁻¹) _) ^ 2).val
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, sq]; field_simp

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[sq_class_of_rat_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma sq_class_of_rat_unit
  {u : ℚˣ} :
-- imply
  QuotientGroup.mk' (Subgroup.square ℚˣ) u = QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (↑((u : ℚ).num * ↑(u : ℚ).den) : ℚ) (by push_cast exact_mod_cast mul_ne_zero (Rat.num_ne_zero.mpr (Units.ne_zero u)) (Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (u : ℚ).pos)))) := by
-- proof
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_square]
  have hden_ne : ((u : ℚ).den : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (u : ℚ).pos)
  refine ⟨Units.mk0 ((u : ℚ).den : ℚ) hden_ne, Units.ext ?_⟩
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [inv_mul_eq_div, div_eq_iff (Units.ne_zero u)]
  have key : (u : ℚ) * ((u : ℚ).den : ℚ) = ((u : ℚ).num : ℚ) := by
    have := Rat.num_div_den (u : ℚ)
    field_simp at this ⊢; linarith
  have cast_eq : (((u : ℚ).num * ((u : ℚ).den : ℤ) : ℤ) : ℚ) =
    ((u : ℚ).num : ℚ) * ((u : ℚ).den : ℚ) := by push_cast; ring
  rw [cast_eq, ← key]
  ring

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[int_sq_mul_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma int_sq_mul_squarefree
  {n : ℤ}
-- given
  (hn : n ≠ 0) :
-- imply
  ∃ r s : ℤ, n = r * s ^ 2 ∧ Squarefree r ∧ r ≠ 0 ∧ s ≠ 0 := by
-- proof
  have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n.natAbs
  have ha_ne : a ≠ 0 := by intro h; subst h; simp at hab; exact hn' hab.symm
  have hb_ne : b ≠ 0 := by intro h; subst h; simp at hab; exact hn' hab.symm
  by_cases hn_pos : 0 ≤ n
  · exact ⟨(a : ℤ), (b : ℤ),
    by rw [← Int.natAbs_of_nonneg hn_pos, ← hab]; push_cast; ring,
    Int.squarefree_natCast.mpr ha,
    Int.natCast_ne_zero.mpr ha_ne,
    Int.natCast_ne_zero.mpr hb_ne⟩
  · push Not at hn_pos
    exact ⟨-(a : ℤ), (b : ℤ),
      by linarith [Int.ofNat_natAbs_of_nonpos (le_of_lt hn_pos),
        show (n.natAbs : ℤ) = (b : ℤ) ^ 2 * (a : ℤ) from by rw [← hab]; push_cast; ring],
      by rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs];
        exact Int.squarefree_natCast.mpr ha,
      neg_ne_zero.mpr (Int.natCast_ne_zero.mpr ha_ne),
      Int.natCast_ne_zero.mpr hb_ne⟩

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[sq_class_of_sq_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma sq_class_of_sq_factor
  {n r s : ℤ}
-- given
  (hn : n ≠ 0)
  (hr : r ≠ 0)
  (hs : s ≠ 0)
  (heq : n = r * s ^ 2) :
-- imply
  QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (n : ℚ) (Int.cast_ne_zero.mpr hn)) = QuotientGroup.mk' (Subgroup.square ℚˣ) (Units.mk0 (r : ℚ) (Int.cast_ne_zero.mpr hr)) := by
-- proof
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_square]
  refine ⟨(Units.mk0 (s : ℚ) (Int.cast_ne_zero.mpr hs))⁻¹, Units.ext ?_⟩
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hr' : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  field_simp
  push_cast [heq]
  ring

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[corollary_25_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma corollary_25_6
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {data : TwoIsogenyData W} :
-- imply
  data.phi.range.FiniteIndex ∧ data.phi_hat.range.FiniteIndex := by
-- proof
  constructor
  ·
    rw [← lemma_25_3_phi data]
    exact AddSubgroup.finiteIndex_ker data.descentMap
  ·
    rw [← lemma_25_3_phi_hat data]
    exact AddSubgroup.finiteIndex_ker data.descentMap'

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[corollary_25_7_index](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma corollary_25_7_index
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {data : TwoIsogenyData W} :
-- imply
  (zsmulAddGroupHom (2 : ℤ) : W.toAffine.Point →+ W.toAffine.Point).range.index = data.phi.range.index * data.phi_hat.range.index := by
-- proof
  rw [← data.comp_eq, AddMonoidHom.range_comp, AddSubgroup.index_map,
    sup_eq_left.mpr data.phi_hat_ker_le_phi_range]

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[corollary_25_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma corollary_25_7
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {data : TwoIsogenyData W} :
-- imply
  (zsmulAddGroupHom (2 : ℤ) : W.toAffine.Point →+ W.toAffine.Point).range.FiniteIndex := by
-- proof
  obtain ⟨hphi, hphi_hat⟩ := corollary_25_6 W data
  rw [AddSubgroup.finiteIndex_iff, corollary_25_7_index W data]
  exact mul_ne_zero hphi.index_ne_zero hphi_hat.index_ne_zero

end EllipticCurve.WeakMordellWeil

namespace EllipticCurve.WeakMordellWeil

/--
[corollary_25_7'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma corollary_25_7'
  {W : WeierstrassCurve ℚ}
  [W.IsElliptic]
  {data : TwoIsogenyData W} :
-- imply
  Empty.Finite (W.toAffine.Point ⧸ (zsmulAddGroupHom (2 : ℤ) : W.toAffine.Point →+ W.toAffine.Point).range) := by
-- proof
  haveI := corollary_25_7 W data
  infer_instance
end EllipticCurve.WeakMordellWeil
noncomputable section
open Filter Topology


namespace CanonicalHeight

/--
[canonicalHeightSeq_double](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma canonicalHeightSeq_double
  [AddCommGroup E]
  {P : E}
  {n : ℕ}
-- given
  (h : E → ℝ) :
-- imply
  canonicalHeightSeq h ((2 : ℤ) • P) n = 4 * canonicalHeightSeq h P (n + 1) := by
-- proof
  simp only [canonicalHeightSeq]
  have key : (2 ^ n : ℤ) • ((2 : ℤ) • P) = (2 ^ (n + 1) : ℤ) • P := by
    rw [smul_smul, pow_succ]
  rw [key, pow_succ]
  ring

end CanonicalHeight

namespace CanonicalHeight

/--
[canonicalHeight_double](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma canonicalHeight_double
  [AddCommGroup E]
  {P : E}
-- given
  (h : E → ℝ)
  (hconv : Tendsto (canonicalHeightSeq h P) atTop (𝓝 (canonicalHeight h P))) :
-- imply
  canonicalHeight h ((2 : ℤ) • P) = 4 * canonicalHeight h P := by
-- proof
  have hseq : canonicalHeightSeq h ((2 : ℤ) • P) =
    fun n => 4 * canonicalHeightSeq h P (n + 1) :=
    funext (canonicalHeightSeq_double h P)
  have hshift : Tendsto (fun n => canonicalHeightSeq h P (n + 1)) atTop
    (𝓝 (canonicalHeight h P)) :=
    hconv.comp (tendsto_add_atTop_nat 1)
  have htend : Tendsto (canonicalHeightSeq h ((2 : ℤ) • P)) atTop
    (𝓝 (4 * canonicalHeight h P)) := by
    rw [hseq]; exact hshift.const_mul 4
  exact htend.limUnder_eq
end CanonicalHeight
section EllipticCurveCanonicalHeight
open CanonicalHeight
attribute [local instance] Classical.dec


namespace TateTheorem

/--
[tateSeq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tateSeq_zero
  {φ : S → S}
  {r : ℝ}
  {x : S}
-- given
  (h : S → ℝ) :
-- imply
  tateSeq φ h r x 0 = h x := by
-- proof
simp [tateSeq]

end TateTheorem

namespace TateTheorem

/--
[tateSeq_dist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tateSeq_dist
  {φ : S → S}
  {r : ℝ}
  {C : ℝ}
  {x : S}
  {n : ℕ}
-- given
  (h : S → ℝ)
  (hr : 1 < r)
  (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) :
-- imply
  dist (tateSeq φ h r x n) (tateSeq φ h r x (n + 1)) ≤ C / r ^ (n + 1) := by
-- proof
  rw [Real.dist_eq]
  have hr_pos : (0 : ℝ) < r := by linarith
  have hrn1_pos : (0 : ℝ) < r ^ (n + 1) := pow_pos hr_pos (n + 1)
  simp only [tateSeq, Function.iterate_succ', Function.comp_def]
  have key : h (φ^[n] x) / r ^ n - h (φ (φ^[n] x)) / r ^ (n + 1) =
    (r * h (φ^[n] x) - h (φ (φ^[n] x))) / r ^ (n + 1) := by
    rw [pow_succ']; field_simp
  rw [key, abs_div, abs_of_pos hrn1_pos, abs_sub_comm]
  exact div_le_div_of_nonneg_right (hbound (φ^[n] x)) hrn1_pos.le

end TateTheorem

namespace TateTheorem

/--
[summable_tate_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma summable_tate_bound
  {r : ℝ}
  {C : ℝ}
-- given
  (hr : 1 < r) :
-- imply
  Summable (fun n => C / r ^ (n + 1)) := by
-- proof
  have hinv_nn : 0 ≤ r⁻¹ := by positivity
  have hinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have : (fun n => C / r ^ (n + 1)) = fun n => C / r * (r⁻¹) ^ n := by
    ext n; simp [pow_succ', div_mul_eq_mul_div]; ring
  rw [this]
  exact (summable_geometric_of_lt_one hinv_nn hinv).mul_left (C / r)

end TateTheorem

namespace TateTheorem

/--
[tsum_tate_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tsum_tate_bound
  {r : ℝ}
  {C : ℝ}
-- given
  (hr : 1 < r) :
-- imply
  ∑' (n : ℕ), C / r ^ (n + 1) = C / (r - 1) := by
-- proof
  have hinv_nn : 0 ≤ r⁻¹ := by positivity
  have hinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have : (fun n => C / r ^ (n + 1)) = fun n => C / r * (r⁻¹) ^ n := by
    ext n; simp [pow_succ', div_mul_eq_mul_div]; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one hinv_nn hinv]
  rw [show (1 : ℝ) - r⁻¹ = (r - 1) / r from by field_simp]
  field_simp

end TateTheorem

namespace TateTheorem

/--
[tateSeq_cauchySeq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tateSeq_cauchySeq
  {φ : S → S}
  {r : ℝ}
  {C : ℝ}
  {x : S}
-- given
  (h : S → ℝ)
  (hr : 1 < r)
  (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) :
-- imply
  CauchySeq (tateSeq φ h r x) :=
-- proof
  cauchySeq_of_dist_le_of_summable _ (tateSeq_dist φ h r hr C hbound x)
    (summable_tate_bound hr C)

end TateTheorem

namespace TateTheorem

/--
[tateSeq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tateSeq_tendsto
  {φ : S → S}
  {r : ℝ}
  {C : ℝ}
  {x : S}
-- given
  (h : S → ℝ)
  (hr : 1 < r)
  (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) :
-- imply
  Tendsto (tateSeq φ h r x) atTop (𝓝 (limUnder atTop (tateSeq φ h r x))) := by
-- proof
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (tateSeq_cauchySeq φ h r hr C hbound x)
  rwa [hL.limUnder_eq]

end TateTheorem

namespace TateTheorem

/--
[tateSeq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tateSeq_comp
  {φ : S → S}
  {r : ℝ}
  {x : S}
  {n : ℕ}
-- given
  (h : S → ℝ)
  (hr : 1 < r) :
-- imply
  tateSeq φ h r (φ x) n = r * tateSeq φ h r x (n + 1) := by
-- proof
  simp only [tateSeq]
  rw [show φ^[n] (φ x) = φ^[n + 1] x from (Function.iterate_succ_apply φ n x).symm,
    pow_succ']
  field_simp

end TateTheorem

namespace TateTheorem

/--
[tate_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tate_bound
  {φ : S → S}
  {r : ℝ}
  {C : ℝ}
  {x : S}
-- given
  (h : S → ℝ)
  (hr : 1 < r)
  (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) :
-- imply
  |limUnder atTop (tateSeq φ h r x) - h x| ≤ C / (r - 1) := by
-- proof
  have htend := tateSeq_tendsto φ h r hr C hbound x
  have hd := dist_le_tsum_of_dist_le_of_tendsto₀ _
    (tateSeq_dist φ h r hr C hbound x) (summable_tate_bound hr C) htend
  rw [tateSeq_zero, Real.dist_eq] at hd
  linarith [tsum_tate_bound r hr C,
    abs_sub_comm (h x) (limUnder atTop (tateSeq φ h r x))]

end TateTheorem

namespace TateTheorem

/--
[tate_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tate_comp_eq
  {φ : S → S}
  {r : ℝ}
  {C : ℝ}
  {x : S}
-- given
  (h : S → ℝ)
  (hr : 1 < r)
  (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) :
-- imply
  limUnder atTop (tateSeq φ h r (φ x)) = r * limUnder atTop (tateSeq φ h r x) := by
-- proof
  have hseq : tateSeq φ h r (φ x) = fun n => r * tateSeq φ h r x (n + 1) :=
    funext (tateSeq_comp φ h r hr x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (tateSeq_cauchySeq φ h r hr C hbound x)
  have hshift : Tendsto (fun n => tateSeq φ h r x (n + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_add_atTop_nat 1)
  have htend_phi : Tendsto (tateSeq φ h r (φ x)) atTop (𝓝 (r * L)) := by
    rw [hseq]; exact hshift.const_mul r
  rw [htend_phi.limUnder_eq, hL.limUnder_eq]

end TateTheorem

namespace TateTheorem

/--
[iterate_eq_of_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma iterate_eq_of_comp
  {φ : S → S}
  {f : S → ℝ}
  {r : ℝ}
  {x : S}
  {n : ℕ}
-- given
  (hf_comp : ∀ x, f (φ x) = r * f x) :
-- imply
  f (φ^[n] x) = r ^ n * f x := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_def, hf_comp, ih]; ring

end TateTheorem

namespace TateTheorem

/--
[tateSeq_const_of_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tateSeq_const_of_comp
  {φ : S → S}
  {f : S → ℝ}
  {r : ℝ}
  {x : S}
  {n : ℕ}
-- given
  (hr : 1 < r)
  (hf_comp : ∀ x, f (φ x) = r * f x) :
-- imply
  tateSeq φ f r x n = f x := by
-- proof
  simp only [tateSeq, iterate_eq_of_comp φ f r hf_comp x n]
  exact mul_div_cancel_left₀ _
    (pow_ne_zero n (ne_of_gt (show (0 : ℝ) < r by linarith)))

end TateTheorem

namespace TateTheorem

/--
[tendsto_div_pow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tendsto_div_pow_zero
  {r : ℝ}
  {D : ℝ}
-- given
  (hr : 1 < r) :
-- imply
  Tendsto (fun n : ℕ => D / r ^ n) atTop (𝓝 0) := by
-- proof
  rw [show (fun n : ℕ => D / r ^ n) = fun n => D * (r⁻¹ ^ n) from by
    ext n; rw [div_eq_mul_inv, inv_pow]]
  rw [show (0 : ℝ) = D * 0 from (mul_zero D).symm]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    (inv_lt_one_of_one_lt₀ hr)).const_mul D

end TateTheorem

namespace TateTheorem

/--
[tateSeq_diff_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tateSeq_diff_bound
  {φ : S → S}
  {r : ℝ}
  {D : ℝ}
  {x : S}
  {n : ℕ}
-- given
  (f h : S → ℝ)
  (hr : 1 < r)
  (hD : ∀ x, |f x - h x| ≤ D) :
-- imply
  ‖tateSeq φ f r x n - tateSeq φ h r x n‖ ≤ D / r ^ n := by
-- proof
  simp only [tateSeq, Real.norm_eq_abs, ← sub_div, abs_div,
    abs_of_pos (pow_pos (show (0 : ℝ) < r by linarith) n)]
  exact div_le_div_of_nonneg_right (hD (φ^[n] x))
    (pow_pos (show (0 : ℝ) < r by linarith) n).le

end TateTheorem

namespace TateTheorem

/--
[tate_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tate_unique
  {φ : S → S}
  {r : ℝ}
  {C : ℝ}
  {f : S → ℝ}
  {D : ℝ}
  {x : S}
-- given
  (h : S → ℝ)
  (hr : 1 < r)
  (hbound : ∀ x, |h (φ x) - r * h x| ≤ C)
  (hD : ∀ x, |f x - h x| ≤ D)
  (hf_comp : ∀ x, f (φ x) = r * f x) :
-- imply
  f x = limUnder atTop (tateSeq φ h r x) := by
-- proof
  obtain ⟨Lh, hLh⟩ := cauchySeq_tendsto_of_complete
    (tateSeq_cauchySeq φ h r hr C hbound x)
  rw [hLh.limUnder_eq]
  have hdiff_zero : Tendsto (fun n => tateSeq φ f r x n - tateSeq φ h r x n)
    atTop (𝓝 0) :=
    squeeze_zero_norm (tateSeq_diff_bound φ f h r hr D hD x)
      (tendsto_div_pow_zero r hr D)
  have : (fun n => tateSeq φ f r x n - tateSeq φ h r x n) =
    (fun n => f x - tateSeq φ h r x n) := by
    ext n; rw [tateSeq_const_of_comp φ f r hr hf_comp x]
  rw [this] at hdiff_zero
  linarith [tendsto_nhds_unique (Tendsto.sub tendsto_const_nhds hLh) hdiff_zero]

end TateTheorem

namespace TateTheorem

/--
[tate_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma tate_theorem
  {φ : S → S}
  {r : ℝ}
  {C : ℝ}
-- given
  (h : S → ℝ)
  (hr : 1 < r)
  (hbound : ∀ x, |h (φ x) - r * h x| ≤ C) :
-- imply
  (∀ x, ∃ L, Tendsto (tateSeq φ h r x) atTop (𝓝 L)) ∧ (∀ x, |limUnder atTop (tateSeq φ h r x) - h x| ≤ C / (r - 1)) ∧ (∀ x, limUnder atTop (tateSeq φ h r (φ x)) = r * limUnder atTop (tateSeq φ h r x)) ∧ (∀ (f : S → ℝ) (D : ℝ), (∀ x, |f x - h x| ≤ D) → (∀ x, f (φ x) = r * f x) → ∀ x, f x = limUnder atTop (tateSeq φ h r x)) :=
-- proof
  ⟨fun x => cauchySeq_tendsto_of_complete (tateSeq_cauchySeq φ h r hr C hbound x),
    fun x => tate_bound φ h r hr C hbound x,
    fun x => tate_comp_eq φ h r hr C hbound x,
    fun f D hD hf x => tate_unique φ h r hr C hbound f D hD hf x⟩
end TateTheorem
end
noncomputable section
open Height Polynomial Set


namespace Northcott

/--
[finite_roots_of_bounded_mahler_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma finite_roots_of_bounded_mahler_degree
  {d : ℕ}
  {B : NNReal} :
-- imply
  Set.Finite {α : ℂ | ∃ p : ℤ[X], p ≠ 0 ∧ p.natDegree ≤ d ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B ∧ (p.map (Int.castRingHom ℂ)).IsRoot α} := by
-- proof
  have hfin_polys := Polynomial.finite_mahlerMeasure_le d B
  have hfin_union : (⋃ p ∈ {p : ℤ[X] | p.natDegree ≤ d ∧
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B},
    ((p.map (Int.castRingHom ℂ)).rootSet ℂ : Set ℂ)).Finite :=
    hfin_polys.biUnion (fun p _ => Polynomial.rootSet_finite _ ℂ)
  apply hfin_union.subset
  intro α hα
  obtain ⟨p, hp_ne, hp_deg, hp_mahler, hp_root⟩ := hα
  simp only [Set.mem_iUnion]
  refine ⟨p, ⟨hp_deg, hp_mahler⟩, ?_⟩
  rw [Polynomial.mem_rootSet]
  exact ⟨(Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hp_ne, hp_root⟩

end Northcott

namespace Northcott

/--
[finite_of_mulHeight₁_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma finite_of_mulHeight₁_le (K : Type*) [Field K] [NumberField K] (B : ℝ) :
  {x : K | mulHeight₁ x ≤ B}.Finite := by
  by_cases hB : B < 1
  · apply Set.Finite.subset (Set.finite_empty)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    linarith [one_le_mulHeight₁ x]
  push Not at hB
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  set B' : NNReal := ⟨B, hB0⟩
  obtain ⟨σ⟩ := NumberField.Embeddings.instNonemptyRingHom K ℂ
  set d := Module.finrank ℚ K
  have hfin := finite_roots_of_bounded_mahler_degree d (B' ^ d)
  apply (hfin.preimage (σ.injective.injOn)).subset
  intro x hx
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
  exact exists_intPoly_of_mulHeight₁_le K σ x B' hx

end Northcott

namespace Northcott

/--
[mulHeight₁_le_mulHeight_of_one_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma mulHeight₁_le_mulHeight_of_one_eq {K : Type*} [Field K] [NumberField K]
  {n : ℕ} (x : Fin (n + 1) → K) (_hx : x ≠ 0) (i₀ : Fin (n + 1)) (hi₀ : x i₀ = 1)
  (j : Fin (n + 1)) : mulHeight₁ (x j) ≤ mulHeight x := by
  let f : Fin 2 → Fin (n + 1) := ![j, i₀]
  rw [mulHeight₁_eq_mulHeight, show (1 : K) = x i₀ from hi₀.symm]
  have hcomp : ![x j, x i₀] = x ∘ f := by
    ext i; fin_cases i <;> simp [f]
  rw [hcomp]
  exact mulHeight_comp_le f x

end Northcott

namespace Northcott

/--
[mapCoords_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma mapCoords_injective
  [CommRing K]
  [CommRing L]
  {σ : K →+* L}
  {n : ℕ}
-- given
  (hσ : Function.Injective σ) :
-- imply
  Function.Injective (mapCoords σ n) := by
-- proof
  intro x y h; ext i; exact hσ (congr_fun h i)

end Northcott

namespace Northcott

/--
[northcott_theorem_25_18](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma northcott_theorem_25_18
  {n : ℕ}
  {d : ℕ}
  {B : ℝ} :
-- imply
  Set.Finite {P : Projectivization ℂ (Fin (n + 1) → ℂ) | ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ), Module.finrank ℚ K ≤ d ∧ ∃ (Q : Projectivization K (Fin (n + 1) → K)), Projectivization.mulHeight Q ≤ B ∧ P = Projectivization.map (mapCoords σ n) (mapCoords_injective σ.injective n) Q} := by
-- proof
  classical
  by_cases hB : B < 1
  · apply Set.Finite.subset (Set.finite_empty)
    intro P hP
    obtain ⟨K, _, _, σ, _, Q, hHQ, _⟩ := hP
    linarith [Projectivization.one_le_mulHeight Q]
  push Not at hB
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  set B' : NNReal := ⟨B, hB0⟩
  have hB'1 : (1 : NNReal) ≤ B' := by exact_mod_cast hB
  set R := {α : ℂ | ∃ p : ℤ[X], p ≠ 0 ∧ p.natDegree ≤ d ∧
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ ↑(B' ^ d) ∧
    (p.map (Int.castRingHom ℂ)).IsRoot α}
  have hR_fin : R.Finite := finite_roots_of_bounded_mahler_degree d (B' ^ d)
  have hT_fin : {v : Fin (n+1) → ℂ | ∀ j, v j ∈ R}.Finite :=
    (Set.Finite.pi (fun _ => hR_fin)).subset (fun v hv j _ => hv j)
  set e : Fin (n + 1) → ℂ := Function.update 0 0 1 with he_def
  have he_ne : e ≠ 0 := by
    intro h; have := congr_fun h 0; simp [he_def, Function.update_self] at this
  apply (hT_fin.image (fun v => if hv : v = 0 then
    Projectivization.mk ℂ e he_ne
    else Projectivization.mk ℂ v hv)).subset
  intro P hP
  simp only [Set.mem_setOf_eq] at hP
  obtain ⟨K, hFK, hNFK, σ, hd, Q, hHQ, hPQ⟩ := hP
  simp only [Set.mem_image, Set.mem_setOf_eq]
  have hq_ne : Q.rep ≠ 0 := Projectivization.rep_nonzero Q
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, Q.rep i₀ ≠ 0 := by
    by_contra h; push Not at h; exact hq_ne (funext h)
  let c := (Q.rep i₀)⁻¹
  let y := c • Q.rep
  have hc_ne : c ≠ 0 := inv_ne_zero hi₀
  have hy_ne : y ≠ 0 := by
    intro h; exact hq_ne ((smul_eq_zero.mp h).resolve_left hc_ne)
  have hy_i₀ : y i₀ = 1 := by
    show (Q.rep i₀)⁻¹ * Q.rep i₀ = 1; exact inv_mul_cancel₀ hi₀
  have hQ_eq : Q = Projectivization.mk K y hy_ne := by
    rw [← Projectivization.mk_rep Q, Projectivization.mk_eq_mk_iff']
    exact ⟨c⁻¹, by show c⁻¹ • y = Q.rep; rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul]⟩
  have hHy : mulHeight y ≤ B := by
    show mulHeight (c • Q.rep) ≤ B
    rw [mulHeight_smul_eq_mulHeight Q.rep hc_ne,
      ← Projectivization.mulHeight_mk (Projectivization.rep_nonzero Q),
      Projectivization.mk_rep]
    exact hHQ
  have hy_bdd : ∀ j, mulHeight₁ (y j) ≤ B :=
    fun j => le_trans (mulHeight₁_le_mulHeight_of_one_eq y hy_ne i₀ hy_i₀ j) hHy
  let w : Fin (n+1) → ℂ := fun j => σ (y j)
  have hw_ne : w ≠ 0 := by
    intro h
    have : w i₀ = 0 := congr_fun h i₀
    simp only [w, hy_i₀, map_one] at this
    exact one_ne_zero this
  have hw_mem : ∀ j, w j ∈ R := by
    intro j
    have hxB : mulHeight₁ (y j) ≤ B' := hy_bdd j
    obtain ⟨p, hp_ne, hp_deg, hp_mahler, hp_root⟩ :=
      exists_intPoly_of_mulHeight₁_le K σ (y j) B' hxB
    refine ⟨p, hp_ne, le_trans hp_deg hd, ?_, hp_root⟩
    calc (p.map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ ↑(B' ^ Module.finrank ℚ K) := hp_mahler
      _ ≤ ↑(B' ^ d) := by
        exact_mod_cast pow_le_pow_right₀ hB'1 hd
  refine ⟨w, hw_mem, ?_⟩
  rw [dif_neg hw_ne]
  rw [hPQ, hQ_eq, Projectivization.map_mk]
  congr 1
end Northcott
end
noncomputable section
open AddSubgroup Set


/--
[addGroup_fg_of_height_descent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma addGroup_fg_of_height_descent
  [AddCommGroup G]
  {ĥ : G → ℝ}
-- given
  (hĥ_nonneg : ∀ P : G, 0 ≤ ĥ P)
  (hĥ_double : ∀ P : G, ĥ ((2 : ℤ) • P) = 4 * ĥ P)
  (hĥ_par : ∀ P Q : G, ĥ (P + Q) + ĥ (P - Q) = 2 * ĥ P + 2 * ĥ Q)
  (hquot : Empty.Finite (G ⧸ (zsmulAddGroupHom (2 : ℤ) : G →+ G).range))
  (hNorthcott : ∀ B : ℝ, {P : G | ĥ P ≤ B}.Finite) :
-- imply
  AddGroup.FG G := by
-- proof
  classical
  rw [AddGroup.fg_iff]
  set H := (zsmulAddGroupHom (2 : ℤ) : G →+ G).range
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set reps : Finset G := Finset.univ.image (fun q : G ⧸ H => q.out)
  have hreps : ∀ Q : G, ∃ P ∈ reps, ∃ R : G, Q - P = (2 : ℤ) • R := by
    intro Q
    let q : G ⧸ H := QuotientAddGroup.mk Q
    refine ⟨q.out, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    have hrel : (QuotientAddGroup.leftRel H) q.out Q := Quotient.mk_out Q
    rw [QuotientAddGroup.leftRel_apply] at hrel
    obtain ⟨_, hm⟩ := hrel
    exact ⟨_, by rw [show Q - q.out = -q.out + Q from by abel]; exact hm.symm⟩
  have hreps_nonempty : reps.Nonempty :=
    ⟨(QuotientAddGroup.mk (0 : G) : G ⧸ H).out,
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨Pmax, _, hPmax⟩ := Finset.exists_max_image reps ĥ hreps_nonempty
  set B := ĥ Pmax
  set S : Set G := {P | ĥ P ≤ B}
  have hS_fin : S.Finite := hNorthcott B
  have hreps_sub : ↑reps ⊆ S := fun P hP => hPmax P (by exact_mod_cast hP)
  suffices AddSubgroup.closure S = ⊤ from ⟨S, this, hS_fin⟩
  by_contra hne
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀, Q₀ ∉ (AddSubgroup.closure S : Set G) := by
    by_contra h; push Not at h; exact hne (eq_top_iff.mpr (fun x _ => h x))
  set bad : Set G := {Q | Q ∉ (AddSubgroup.closure S : Set G)} ∩ {Q | ĥ Q ≤ ĥ Q₀}
  have hbad_fin : bad.Finite := (hNorthcott (ĥ Q₀)).subset inter_subset_right
  have hbad_ne : bad.Nonempty := ⟨Q₀, hQ₀, Set.mem_setOf.mpr le_rfl⟩
  obtain ⟨Q, hQ_bad, hQ_min⟩ :=
    hbad_fin.toFinset.exists_min_image ĥ (by rwa [Set.Finite.toFinset_nonempty])
  rw [Set.Finite.mem_toFinset] at hQ_bad
  have hQ_not := hQ_bad.1
  have hQ_le₀ := hQ_bad.2
  have hQ_global_min : ∀ Q' : G, Q' ∉ (AddSubgroup.closure S : Set G) → ĥ Q ≤ ĥ Q' := by
    intro Q' hQ'
    by_cases h : ĥ Q' ≤ ĥ Q₀
    · exact hQ_min Q' (by rw [Set.Finite.mem_toFinset]; exact ⟨hQ', h⟩)
    · push Not at h; exact le_trans hQ_le₀ (le_of_lt h)
  obtain ⟨P, hP_mem, R, hQPR⟩ := hreps Q
  have hP_cl : P ∈ (AddSubgroup.closure S : Set G) :=
    AddSubgroup.subset_closure (hreps_sub hP_mem)
  have hR_not : R ∉ (AddSubgroup.closure S : Set G) := by
    intro hR
    exact hQ_not ((show Q = P + (2 : ℤ) • R from by rw [← hQPR]; abel) ▸
      (AddSubgroup.closure S).add_mem hP_cl ((AddSubgroup.closure S).zsmul_mem hR 2))
  have hR_ge : ĥ Q ≤ ĥ R := hQ_global_min R hR_not
  have hP_le : ĥ P ≤ B := hreps_sub hP_mem
  have hpar := hĥ_par Q P
  have hĥQP : ĥ (Q - P) = 4 * ĥ R := by rw [hQPR, hĥ_double]
  have : 2 * ĥ Q ≤ 2 * ĥ P := by
    have h1 : 4 * ĥ R ≤ 2 * ĥ Q + 2 * ĥ P := by
      calc 4 * ĥ R = ĥ (Q - P) := hĥQP.symm
        _ ≤ ĥ (Q + P) + ĥ (Q - P) := le_add_of_nonneg_left (hĥ_nonneg _)
        _ = 2 * ĥ Q + 2 * ĥ P := hpar
    linarith
  exact hQ_not (AddSubgroup.subset_closure (show ĥ Q ≤ B by linarith))
section Theorem_25_14
open Height MvPolynomial

/--
[theorem_25_14_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
lemma theorem_25_14_upper_bound
  [Field K]
  [NumberField K]
  {n m : ℕ}
  {d : ℕ}
  {φ : Fin (m + 1) → MvPolynomial (Fin (n + 1)) K}
-- given
  (hφ : IsProjectiveMorphism d φ) :
-- imply
  ∃ C₁ : ℝ, ∀ (x : Fin (n + 1) → K), logHeight (fun j => (φ j).eval x) ≤ C₁ + ↑d * logHeight x :=
-- proof
  logHeight_eval_le' hφ.1
end Theorem_25_14
end

/--
[NumberField.FinitePlace.isFinitePlace_comp_galois](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
private lemma isFinitePlace_comp_galois_eq
  [Field K]
  [NumberField K]
  {σ : K ≃ₐ[ℚ] K}
  {v : NumberField.FinitePlace K} :
-- imply
  ∃ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), place (NumberField.FinitePlace.embedding w) = v.val.comp (f := (σ.symm : K →+* K)) σ.symm.injective := by
-- proof
  apply NumberField.FinitePlace.isFinitePlace_comp_galois σ v

/--
[finite_of_mulHeight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
private lemma finite_of_mulHeight_eq
  {K : Type*}
  [Field K]
  [NumberField K]
  {B : ℝ} :
-- imply
  {x : K | mulHeight₁ x ≤ B}.Finite := by
-- proof
  apply Northcott.finite_of_mulHeight K B

/--
[mulHeight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean)
-/
@[path]
private lemma mulHeight_eq
  [Field K]
  [NumberField K]
  {n : ℕ}
  {x : Fin (n + 1) → K}
  {i₀ : Fin (n + 1)}
  {j : Fin (n + 1)}
-- given
  (_hx : x ≠ 0)
  (hi₀ : x i₀ = 1) :
-- imply
  mulHeight₁ (x j) ≤ mulHeight x := by
-- proof
  apply Northcott.mulHeight x _hx i₀ hi₀ j


-- created on 2026-10-23
