import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.EndomorphismNorm.Part2
open PositiveDefiniteInvolutionAlgebra WeierstrassCurve WeierstrassCurve.Affine
open scoped TensorProduct


namespace PositiveDefiniteInvolutionAlgebra

/--
[invol_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma invol_zero
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A] :
-- imply
  invol (0 : A) = 0 := by
-- proof
  have h := invol_add (0 : A) (0 : A)
  rw [add_zero] at h
  have : invol (0 : A) + invol (0 : A) = invol (0 : A) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

end PositiveDefiniteInvolutionAlgebra

/--
[PositiveDefiniteInvolutionAlgebra.algebraMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma PositiveDefiniteInvolutionAlgebra.algebraMap_injective
  [Ring A]
  [Algebra ℚ A]
  [Nontrivial A] :
-- imply
  Function.Injective (algebraMap ℚ A) := by
-- proof
  intro x y hxy
  by_contra h
  have hne : x - y ≠ 0 := sub_ne_zero.mpr h
  have h0 : (algebraMap ℚ A) (x - y) = 0 := by rw [map_sub, sub_eq_zero.mpr hxy]
  have h1 : (x - y)⁻¹ • (algebraMap ℚ A) (x - y) = 0 := by rw [h0, smul_zero]
  rw [Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hne, one_smul] at h1
  exact one_ne_zero h1
namespace PositiveDefiniteInvolutionAlgebra
variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

namespace PositiveDefiniteInvolutionAlgebra

/--
[normMap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma normMap_zero
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A] :
-- imply
  normMap (0 : A) = 0 := by
-- proof
  have h := normMap_spec (0 : A)
  rw [zero_mul] at h
  have : (algebraMap ℚ A) (normMap (0 : A)) = (algebraMap ℚ A) 0 := by
    rw [h.symm, map_zero]
  exact algebraMap_injective this

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[normMap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma normMap_nonneg
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A} :
-- imply
  0 ≤ normMap a := by
-- proof
  by_cases ha : a = 0
  · rw [ha, normMap_zero]
  · exact le_of_lt (normMap_pos a ha)

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[normMap_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma normMap_eq_zero_iff
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A} :
-- imply
  normMap a = 0 ↔ a = 0 := by
-- proof
  constructor
  · intro h
    by_contra ha
    exact absurd h (ne_of_gt (normMap_pos a ha))
  · intro h
    rw [h, normMap_zero]

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[normMap_invol](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma normMap_invol
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A} :
-- imply
  normMap (invol a) = normMap a := by
-- proof
  by_cases ha : a = 0
  · subst ha; simp only [invol_zero, normMap_zero]
  · have h1 : invol a * a = (algebraMap ℚ A) (normMap (invol a)) := by
    have := normMap_spec (invol a)
    rwa [invol_invol] at this
    have h2 : a * invol a = (algebraMap ℚ A) (normMap a) := normMap_spec a
    have h3 : a * (invol a * a) = (a * invol a) * a := (mul_assoc a (invol a) a).symm
    rw [h1, h2, Algebra.commutes] at h3
    have h4 : a * ((algebraMap ℚ A) (normMap (invol a)) - (algebraMap ℚ A) (normMap a)) = 0 := by
      rw [mul_sub, h3, sub_self]
    obtain h5 | h5 := eq_zero_or_eq_zero_of_mul_eq_zero _ _ h4
    · exact absurd h5 ha
    · rw [← map_sub] at h5
      have := algebraMap_injective (show (algebraMap ℚ A) (normMap (invol a) - normMap a) =
        (algebraMap ℚ A) (0 : ℚ) from by rw [h5, map_zero])
      linarith

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[normMap_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma normMap_mul
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a b : A} :
-- imply
  normMap (a * b) = normMap a * normMap b := by
-- proof
  have h1 := normMap_spec (a * b)
  rw [invol_mul] at h1
  have h2 : a * b * (invol b * invol a) = a * (b * invol b) * invol a := by
    simp only [mul_assoc]
  rw [normMap_spec b] at h2
  have h3 : a * (algebraMap ℚ A) (normMap b) * invol a =
    (algebraMap ℚ A) (normMap b) * (a * invol a) := by
    rw [← Algebra.commutes (normMap b) a, mul_assoc]
  rw [normMap_spec a, ← map_mul] at h3
  rw [h2, h3] at h1
  have h4 := algebraMap_injective h1
  linarith

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[isUnit_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma isUnit_of_ne_zero
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A}
-- given
  (ha : a ≠ 0) :
-- imply
  IsUnit a := by
-- proof
  let Na := normMap a
  let ahat := invol a
  have hNa_pos : 0 < Na := normMap_pos a ha
  have hNa_ne : Na ≠ 0 := ne_of_gt hNa_pos
  let b := (Na⁻¹ : ℚ) • ahat
  have h_spec : a * ahat = (algebraMap ℚ A) Na := normMap_spec a
  have h_mul_right : a * b = 1 := by
    show a * ((Na⁻¹ : ℚ) • ahat) = 1
    rw [Algebra.mul_smul_comm, h_spec, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]
  have h_spec_invol : ahat * a = (algebraMap ℚ A) Na := by
    have := normMap_spec (invol a)
    rwa [invol_invol, normMap_invol] at this
  have h_mul_left : b * a = 1 := by
    show (Na⁻¹ : ℚ) • ahat * a = 1
    rw [Algebra.smul_mul_assoc, h_spec_invol, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]
  exact ⟨⟨a, b, h_mul_right, h_mul_left⟩, rfl⟩

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[inverse_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma inverse_eq
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A}
-- given
  (ha : a ≠ 0) :
-- imply
  a * ((normMap a)⁻¹ • invol a) = 1 ∧ ((normMap a)⁻¹ • invol a) * a = 1 := by
-- proof
  have hNa_ne : normMap a ≠ 0 := ne_of_gt (normMap_pos a ha)
  constructor
  · rw [Algebra.mul_smul_comm, normMap_spec a, Algebra.algebraMap_eq_smul_one,
    smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]
  · have h : invol a * a = (algebraMap ℚ A) (normMap a) := by
    have := normMap_spec (invol a)
    rwa [invol_invol, normMap_invol] at this
    rw [Algebra.smul_mul_assoc, h, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ hNa_ne, one_smul]
end PositiveDefiniteInvolutionAlgebra
namespace WeierstrassCurve.Affine
universe u

end PositiveDefiniteInvolutionAlgebra

namespace WeierstrassCurve.Affine

/--
[End0.N_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma End0.N_spec
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  letI := EndomorphismAlgebra.instRing E letI := EndomorphismAlgebra.instAlgebra E (algebraMap ℚ (End0 E)) (End0.N E α) = α * End0.dual E α := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  exact (PositiveDefiniteInvolutionAlgebra.normMap_spec α).symm

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.norm_nonneg
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  0 ≤ End0.N E α := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_nonneg α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.norm_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.norm_eq_zero_iff
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  End0.N E α = 0 ↔ α = 0 := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_eq_zero_iff α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.norm_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.norm_dual
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  End0.N E (End0.dual E α) = End0.N E α := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_invol α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.norm_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.norm_mul
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α β : End0 E} :
-- imply
  End0.N E (α * β) = End0.N E α * End0.N E β := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.normMap_mul α β

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.norm_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.norm_properties
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α β : End0 E} :
-- imply
  0 ≤ End0.N E α ∧ (End0.N E α = 0 ↔ α = 0) ∧ End0.N E (End0.dual E α) = End0.N E α ∧ End0.N E (α * β) = End0.N E α * End0.N E β :=
-- proof
  ⟨EndAlgebra.norm_nonneg E α, EndAlgebra.norm_eq_zero_iff E α,
    EndAlgebra.norm_dual E α, EndAlgebra.norm_mul E α β⟩

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.isUnit_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.isUnit_of_ne_zero
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {a : End0 E}
-- given
  (ha : a ≠ 0) :
-- imply
  IsUnit a := by
-- proof
  letI : Ring (End0 E) := EndomorphismAlgebra.instRing E
  letI : Algebra ℚ (End0 E) := EndomorphismAlgebra.instAlgebra E
  letI : PositiveDefiniteInvolutionAlgebra (End0 E) := EndomorphismAlgebra.instPDInvAlgebra E
  letI : Nontrivial (End0 E) := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.isUnit_of_ne_zero a ha

end WeierstrassCurve.Affine

namespace PositiveDefiniteInvolutionAlgebra

/--
[traceMap_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma traceMap_spec
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A} :
-- imply
  (algebraMap ℚ A) (traceMap a) = a + invol a := by
-- proof
  unfold traceMap
  have h1 := normMap_spec (a + 1)
  have h2 := normMap_spec a
  rw [invol_add, invol_one] at h1
  have expand : (a + 1) * (invol a + 1) = a * invol a + a + invol a + 1 := by
    rw [add_mul, mul_add, mul_add, mul_one, one_mul, one_mul]
    abel
  rw [expand, h2] at h1
  rw [map_sub, map_sub, map_one]
  have h3 : (algebraMap ℚ A) (normMap (a + 1)) =
    (algebraMap ℚ A) (normMap a) + (a + invol a) + 1 := by
    rw [← h1]; abel
  rw [h3]; abel

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[invol_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma invol_smul
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  {r : ℚ}
  {a : A} :
-- imply
  invol (r • a) = r • invol a := by
-- proof
  rw [Algebra.smul_def, Algebra.smul_def, invol_mul, invol_rat]
  exact (Algebra.commutes r (invol a)).symm

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[traceMap_invol](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma traceMap_invol
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A} :
-- imply
  traceMap (invol a) = traceMap a := by
-- proof
  apply algebraMap_injective (A := A)
  rw [traceMap_spec, traceMap_spec, invol_invol, add_comm]

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[traceMap_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma traceMap_add
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a b : A} :
-- imply
  traceMap (a + b) = traceMap a + traceMap b := by
-- proof
  apply algebraMap_injective (A := A)
  rw [map_add, traceMap_spec, traceMap_spec, traceMap_spec, invol_add]
  abel

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[traceMap_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma traceMap_smul
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {r : ℚ}
  {a : A} :
-- imply
  traceMap (r • a) = r * traceMap a := by
-- proof
  apply algebraMap_injective (A := A)
  rw [map_mul, traceMap_spec, traceMap_spec, invol_smul]
  rw [Algebra.smul_def, Algebra.smul_def, ← mul_add]

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[char_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma char_poly
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A} :
-- imply
  a ^ 2 - (traceMap a) • a + (normMap a) • (1 : A) = 0 := by
-- proof
  have hT := traceMap_spec a
  have hN := normMap_spec a
  rw [sq, Algebra.smul_def (traceMap a) a, Algebra.smul_def (normMap a) (1 : A), mul_one]
  rw [Algebra.commutes (traceMap a) a]
  rw [hT, mul_add, ← hN]
  abel

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[traceMap_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma traceMap_algebraMap
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {q : ℚ} :
-- imply
  traceMap ((algebraMap ℚ A) q) = 2 * q := by
-- proof
  apply algebraMap_injective (A := A)
  rw [traceMap_spec, invol_rat, ← two_mul, map_mul, map_ofNat]

end PositiveDefiniteInvolutionAlgebra

namespace PositiveDefiniteInvolutionAlgebra

/--
[traceMap_invol_mul_self_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma traceMap_invol_mul_self_pos
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a : A}
-- given
  (ha : a ≠ 0) :
-- imply
  0 < traceMap (invol a * a) := by
-- proof
  have h_spec : invol a * a = (algebraMap ℚ A) (normMap (invol a)) := by
    have := normMap_spec (invol a)
    rwa [invol_invol] at this
  have h_eq : normMap (invol a) = normMap a := normMap_invol a
  rw [show invol a * a = (algebraMap ℚ A) (normMap a) from by rw [h_spec, h_eq]]
  rw [traceMap_algebraMap]
  linarith [normMap_pos a ha]
end PositiveDefiniteInvolutionAlgebra
namespace WeierstrassCurve.Affine
universe u₂


namespace WeierstrassCurve.Affine

/--
[EndAlgebra.trace_rationality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.trace_rationality
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  End0.T E α = 1 + End0.N E α - End0.N E (1 - α) := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  show PositiveDefiniteInvolutionAlgebra.traceMap α =
    1 + PositiveDefiniteInvolutionAlgebra.normMap α -
    PositiveDefiniteInvolutionAlgebra.normMap (1 - α)
  apply PositiveDefiniteInvolutionAlgebra.algebraMap_injective (A := End0 E)
  rw [PositiveDefiniteInvolutionAlgebra.traceMap_spec]
  rw [map_sub, map_add, map_one]
  have hN := PositiveDefiniteInvolutionAlgebra.normMap_spec α
  have hN1 := PositiveDefiniteInvolutionAlgebra.normMap_spec (1 - α)
  have hsub : (1 : End0 E) - α = 1 + (-α) := sub_eq_add_neg 1 α
  have hinv_neg : PositiveDefiniteInvolutionAlgebra.invol (-α) =
    -PositiveDefiniteInvolutionAlgebra.invol α := by
    have h0 := PositiveDefiniteInvolutionAlgebra.invol_zero (A := End0 E)
    have := PositiveDefiniteInvolutionAlgebra.invol_add α (-α)
    rw [add_neg_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hinv_sub : PositiveDefiniteInvolutionAlgebra.invol (1 - α) =
    1 - PositiveDefiniteInvolutionAlgebra.invol α := by
    rw [hsub, PositiveDefiniteInvolutionAlgebra.invol_add,
      PositiveDefiniteInvolutionAlgebra.invol_one, hinv_neg, sub_eq_add_neg]
  rw [hinv_sub] at hN1
  have expand : (1 - α) * (1 - PositiveDefiniteInvolutionAlgebra.invol α) =
    1 - α - PositiveDefiniteInvolutionAlgebra.invol α +
    α * PositiveDefiniteInvolutionAlgebra.invol α := by noncomm_ring
  rw [expand, hN] at hN1
  rw [← hN1]; abel

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.trace_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.trace_dual
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  End0.T E (End0.dual E α) = End0.T E α := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.traceMap_invol α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.trace_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.trace_add
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α β : End0 E} :
-- imply
  End0.T E (α + β) = End0.T E α + End0.T E β := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.traceMap_add α β

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.trace_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.trace_smul
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {r : ℚ}
  {α : End0 E} :
-- imply
  End0.T E (r • α) = r * End0.T E α := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.traceMap_smul r α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.trace_dual_and_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.trace_dual_and_linear
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F} :
-- imply
  (∀ α : End0 E, End0.T E (End0.dual E α) = End0.T E α) ∧ (∀ α : End0 E, End0.T E α = 1 + End0.N E α - End0.N E (1 - α)) ∧ (∀ α β : End0 E, End0.T E (α + β) = End0.T E α + End0.T E β) ∧ (∀ (r : ℚ) (α : End0 E), End0.T E (r • α) = r * End0.T E α) :=
-- proof
  ⟨EndAlgebra.trace_dual E, EndAlgebra.trace_rationality E,
    EndAlgebra.trace_add E, EndAlgebra.trace_smul E⟩

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.char_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.char_poly
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  α ^ 2 - (End0.T E α) • α + (End0.N E α) • (1 : End0 E) = 0 := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  exact PositiveDefiniteInvolutionAlgebra.char_poly α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.char_poly_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.char_poly_dual
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  End0.dual E α ^ 2 - (End0.T E α) • End0.dual E α + (End0.N E α) • (1 : End0 E) = 0 := by
-- proof
  rw [← EndAlgebra.trace_dual E α, ← EndAlgebra.norm_dual E α]
  exact EndAlgebra.char_poly E (End0.dual E α)

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.alpha_is_root_of_char_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.alpha_is_root_of_char_poly
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  letI := EndomorphismAlgebra.instRing E letI := EndomorphismAlgebra.instAlgebra E (Polynomial.aeval α) (End0.charPolyOf E α) = 0 := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  simp only [End0.charPolyOf, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C]
  rw [show (algebraMap ℚ (End0 E)) (End0.T E α) * α = (End0.T E α) • α from
    (Algebra.smul_def (End0.T E α) α).symm]
  rw [show (algebraMap ℚ (End0 E)) (End0.N E α) = (End0.N E α) • (1 : End0 E) from by
    rw [Algebra.smul_def, mul_one]]
  exact EndAlgebra.char_poly E α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.dual_is_root_of_char_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.dual_is_root_of_char_poly
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  letI := EndomorphismAlgebra.instRing E letI := EndomorphismAlgebra.instAlgebra E (Polynomial.aeval (End0.dual E α)) (End0.charPolyOf E α) = 0 := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  simp only [End0.charPolyOf, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C]
  rw [show (algebraMap ℚ (End0 E)) (End0.T E α) * End0.dual E α = (End0.T E α) • End0.dual E α from
    (Algebra.smul_def (End0.T E α) (End0.dual E α)).symm]
  rw [show (algebraMap ℚ (End0 E)) (End0.N E α) = (End0.N E α) • (1 : End0 E) from by
    rw [Algebra.smul_def, mul_one]]
  exact EndAlgebra.char_poly_dual E α

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.roots_of_char_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.roots_of_char_poly
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  letI := EndomorphismAlgebra.instRing E letI := EndomorphismAlgebra.instAlgebra E (Polynomial.aeval α) (End0.charPolyOf E α) = 0 ∧ (Polynomial.aeval (End0.dual E α)) (End0.charPolyOf E α) = 0 :=
-- proof
  ⟨EndAlgebra.alpha_is_root_of_char_poly E α, EndAlgebra.dual_is_root_of_char_poly E α⟩

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[EndAlgebra.rosati_fixed_iff_rational](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
lemma EndAlgebra.rosati_fixed_iff_rational
  {F : Type u₂}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {α : End0 E} :
-- imply
  End0.dual E α = α ↔ ∃ r : ℚ, α = r • 1 := by
-- proof
  letI := EndomorphismAlgebra.instRing E
  letI := EndomorphismAlgebra.instAlgebra E
  letI := EndomorphismAlgebra.instPDInvAlgebra E
  letI := End0.instNontrivial E
  constructor
  ·
    intro h
    have hinv : PositiveDefiniteInvolutionAlgebra.invol α = α := h
    have hT := PositiveDefiniteInvolutionAlgebra.traceMap_spec α
    rw [hinv] at hT
    have h2 : (algebraMap ℚ (End0 E)) (PositiveDefiniteInvolutionAlgebra.traceMap α) = (2 : ℚ) • α := by
      rw [hT, two_smul]
    rw [Algebra.algebraMap_eq_smul_one] at h2
    refine ⟨PositiveDefiniteInvolutionAlgebra.traceMap α / 2, ?_⟩
    have h3 : (2 : ℚ) ≠ 0 := two_ne_zero
    calc α = (2 : ℚ)⁻¹ • ((2 : ℚ) • α) := by rw [inv_smul_smul₀ h3]
      _ = (2 : ℚ)⁻¹ • (PositiveDefiniteInvolutionAlgebra.traceMap α • (1 : End0 E)) := by rw [h2]
      _ = ((2 : ℚ)⁻¹ * PositiveDefiniteInvolutionAlgebra.traceMap α) • (1 : End0 E) := by rw [smul_smul]
      _ = (PositiveDefiniteInvolutionAlgebra.traceMap α / 2) • (1 : End0 E) := by rw [inv_mul_eq_div]
  ·
    rintro ⟨r, rfl⟩
    show PositiveDefiniteInvolutionAlgebra.invol (r • (1 : End0 E)) = r • 1
    rw [PositiveDefiniteInvolutionAlgebra.invol_smul,
      PositiveDefiniteInvolutionAlgebra.invol_one]

end WeierstrassCurve.Affine

/--
[eq_zero_or_eq_zero_of_mul_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean)
-/
@[path]
private lemma eq_zero_or_eq_zero_of_mul_eq_zero_eq
  [Ring A]
  [Algebra ℚ A]
  [PositiveDefiniteInvolutionAlgebra A]
  [Nontrivial A]
  {a b : A}
-- given
  (hab : a * b = 0) :
-- imply
  a = 0 ∨ b = 0 := by
-- proof
  apply PositiveDefiniteInvolutionAlgebra.eq_zero_or_eq_zero_of_mul_eq_zero a b hab


-- created on 2026-10-23
