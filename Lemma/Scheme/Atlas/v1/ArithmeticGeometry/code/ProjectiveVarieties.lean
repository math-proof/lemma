import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties
open MvPolynomial Finsupp HomogeneousPolynomial AffinePatch ProjectiveClosure ProjectiveVarietyDef Theorem1323 Theorem1324 Corollary1326
open scoped LinearAlgebra.Projectivization


namespace HomogeneousPolynomial


namespace ProjectiveClosure

/--
[homogenize_mem_homogenizeIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma homogenize_mem_homogenizeIdeal
  {n : ℕ}
  [CommSemiring R]
  {I : Ideal (MvPolynomial (Fin n) R)}
  {f : MvPolynomial (Fin n) R}
-- given
  (hf : f ∈ I) :
-- imply
  homogenize f ∈ homogenizeIdeal I :=
-- proof
  Ideal.subset_span ⟨f, hf, rfl⟩
variable (k : Type*) [Field k]

end ProjectiveClosure

namespace ProjectiveVarietyDef

/--
[eval_single_homogenized_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma eval_single_homogenized_monomial
  {n : ℕ}
  {k : Type*}
  [Field k]
  {m : Fin n →₀ ℕ}
  {c : k}
  {d : ℕ}
  {P : Fin n → k} :
-- imply
  eval ((0 : Fin (n + 1)).insertNth (1 : k) P) (monomial (m.mapDomain Fin.succ + single 0 (d - m.sum fun _ e => e)) c) = c * m.prod (fun i e => P i ^ e) := by
-- proof
  rw [eval_monomial, prod_add_index (by simp) (by intros; rw [pow_add]),
    prod_mapDomain_index (by simp) (by intros; rw [pow_add]),
    prod_single_index (by simp)]
  simp [Fin.insertNth_apply_same, one_pow]

end ProjectiveVarietyDef

namespace ProjectiveVarietyDef

/--
[eval_homogenize_at_one_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma eval_homogenize_at_one_cons
  {n : ℕ}
  {k : Type*}
  [Field k]
  {f : MvPolynomial (Fin n) k}
  {P : Fin n → k} :
-- imply
  eval ((0 : Fin (n + 1)).insertNth (1 : k) P) (ProjectiveClosure.homogenize f) = eval P f := by
-- proof
  simp only [ProjectiveClosure.homogenize, map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  congr 1; ext m
  rw [eval_single_homogenized_monomial, eval_monomial]

end ProjectiveVarietyDef

namespace ProjectiveVarietyDef

/--
[eval_comp_dehomogenize_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma eval_comp_dehomogenize_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {P : Fin n → k} :
-- imply
  (eval P).comp (AffineParts.dehomogenize k (0 : Fin (n + 1))) = eval ((0 : Fin (n + 1)).insertNth (1 : k) P) := by
-- proof
  apply ringHom_ext
  · intro a; simp [AffineParts.dehomogenize]
  · intro j
    simp only [RingHom.comp_apply, AffineParts.dehomogenize, eval₂Hom_X']
    by_cases hj : j = (0 : Fin (n + 1))
    · subst hj; simp [Fin.insertNth_apply_same]
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj; simp

end ProjectiveVarietyDef

namespace ProjectiveVarietyDef

/--
[eval_dehomogenize_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma eval_dehomogenize_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {g : MvPolynomial (Fin (n + 1)) k}
  {P : Fin n → k} :
-- imply
  eval P (AffineParts.dehomogenize k (0 : Fin (n + 1)) g) = eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g := by
-- proof
  rw [← RingHom.comp_apply, eval_comp_dehomogenize_eq]

end ProjectiveVarietyDef

namespace ProjectiveVarietyDef

/--
[eval_homogenize_dehomogenize_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma eval_homogenize_dehomogenize_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {f : MvPolynomial (Fin (n + 1)) k}
  {P : Fin n → k} :
-- imply
  eval ((0 : Fin (n + 1)).insertNth (1 : k) P) (ProjectiveClosure.homogenize (AffineParts.dehomogenize k 0 f)) = eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f := by
-- proof
  rw [eval_homogenize_at_one_cons, eval_dehomogenize_eq]

end ProjectiveVarietyDef

namespace ProjectiveVarietyDef

/--
[homogenize_dehomogenize_mem_homogenizeIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma homogenize_dehomogenize_mem_homogenizeIdeal
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
  {f : MvPolynomial (Fin (n + 1)) k}
-- given
  (hf : f ∈ I) :
-- imply
  ProjectiveClosure.homogenize (AffineParts.dehomogenize k 0 f) ∈ ProjectiveClosure.homogenizeIdeal (I.map (AffineParts.dehomogenize k 0)) :=
-- proof
  ProjectiveClosure.homogenize_mem_homogenizeIdeal (Ideal.mem_map_of_mem _ hf)

end ProjectiveVarietyDef

namespace ProjectiveVarietyDef

/--
[projective_closure_cap_affine_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma projective_closure_cap_affine_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin n) k)} :
-- imply
  {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0} = {P : Fin n → k | ∀ f ∈ I, eval P f = 0} := by
-- proof
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  ·
    intro hP f hf
    rw [← eval_homogenize_at_one_cons]
    exact hP _ (ProjectiveClosure.homogenize_mem_homogenizeIdeal hf)
  ·
    intro hP g hg
    have hgen : ∀ s ∈ ProjectiveClosure.homogenizeSet I,
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) s = 0 := by
      rintro _ ⟨f, hf, rfl⟩
      rw [eval_homogenize_at_one_cons]
      exact hP f hf
    have hker : ProjectiveClosure.homogenizeIdeal I ≤
      RingHom.ker (eval ((0 : Fin (n + 1)).insertNth (1 : k) P)) := by
      rw [ProjectiveClosure.homogenizeIdeal]
      exact Ideal.span_le.mpr fun s hs => hgen s hs
    exact hker hg
end
noncomputable section
open MvPolynomial
open scoped LinearAlgebra.Projectivization
namespace ProjectiveDimension
variable {n : ℕ} (k : Type*) [Field k]


/--
[isHomogeneous_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma isHomogeneous_zero
  [CommSemiring R]
  {d : ℕ} :
-- imply
  IsHomogeneous (0 : MvPolynomial σ R) :=
-- proof
  ⟨d, MvPolynomial.isHomogeneous_zero σ R d⟩

end HomogeneousPolynomial

namespace HomogeneousPolynomial

/--
[isHomogeneous_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma isHomogeneous_C
  [CommSemiring R]
  {r : R} :
-- imply
  IsHomogeneous (C r : MvPolynomial σ R) :=
-- proof
  ⟨0, MvPolynomial.isHomogeneous_C σ r⟩

end HomogeneousPolynomial

namespace HomogeneousPolynomial

/--
[isHomogeneous_X](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma isHomogeneous_X
  [CommSemiring R]
  {i : σ} :
-- imply
  IsHomogeneous (X i : MvPolynomial σ R) :=
-- proof
  ⟨1, MvPolynomial.isHomogeneous_X R i⟩

end HomogeneousPolynomial

namespace HomogeneousPolynomial

/--
[sum_homogeneousComponent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma sum_homogeneousComponent
  [CommSemiring R]
  {f : MvPolynomial σ R} :
-- imply
  ∑ i ∈ Finset.range (f.totalDegree + 1), homogeneousComponent i f = f :=
-- proof
  MvPolynomial.sum_homogeneousComponent f
end HomogeneousPolynomial
namespace HomogeneousIdealDef
variable (σ : Type*) (R : Type*) [CommSemiring R] [DecidableEq σ]
attribute [local instance] MvPolynomial.gradedAlgebra


namespace ProjectiveClosure

/--
[homogenize_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma homogenize_def
  {n : ℕ}
  [CommSemiring R]
  {f : MvPolynomial (Fin n) R} :
-- imply
  homogenize f = f.support.sum fun m => MvPolynomial.monomial (m.mapDomain Fin.succ + Finsupp.single 0 (f.totalDegree - (m.sum fun _ e => e))) (MvPolynomial.coeff m f) :=
-- proof
  rfl

end ProjectiveClosure

namespace ProjectiveClosure

/--
[projectiveZeroLocus_anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma projectiveZeroLocus_anti
  {n : ℕ}
  [CommSemiring R]
  {k : Type*}
  [Field k]
  {S T : Set (MvPolynomial (Fin (n + 1)) k)}
-- given
  (h : S ⊆ T) :
-- imply
  projectiveZeroLocus k T ⊆ projectiveZeroLocus k S :=
-- proof
  fun _ hp f hf => hp f (h hf)

end ProjectiveClosure

namespace ProjectiveVarietyDef

/--
[IsProjectiveVariety.isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma IsProjectiveVariety.isIrreducible
  {n : ℕ}
  {k : Type*}
  [Field k]
  {V : Set (ℙ k (Fin (n + 1) → k))}
-- given
  (hV : IsProjectiveVariety k V) :
-- imply
  IsIrreducibleProjectiveAlgebraicSet k V :=
-- proof
  hV.2

end ProjectiveVarietyDef

namespace ProjectiveVarietyDef

/--
[IsProjectiveVariety.nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma IsProjectiveVariety.nonempty
  {n : ℕ}
  {k : Type*}
  [Field k]
  {V : Set (ℙ k (Fin (n + 1) → k))}
-- given
  (hV : IsProjectiveVariety k V) :
-- imply
  V.Nonempty :=
-- proof
  hV.2.1
end ProjectiveVarietyDef
end
noncomputable section
open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization


namespace Theorem1323

/--
[dehomogenize_monomial_mapDomain_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma dehomogenize_monomial_mapDomain_succ
  {n : ℕ}
  {k : Type*}
  [Field k]
  {m : Fin n →₀ ℕ}
  {c : k}
  {e : ℕ} :
-- imply
  AffineParts.dehomogenize k (0 : Fin (n + 1)) (monomial (m.mapDomain Fin.succ + Finsupp.single 0 e) c) = monomial m c := by
-- proof
  simp only [AffineParts.dehomogenize]
  rw [eval₂Hom_monomial,
    prod_add_index (by simp) (by intros; rw [pow_add]),
    prod_single_index (by simp),
    prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
  simp only [Fin.insertNth_apply_same, one_pow, mul_one]
  rw [monomial_eq]; congr 1

end Theorem1323

namespace Theorem1324

/--
[dehomogenize_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma dehomogenize_surjective
  {n : ℕ}
  {k : Type*}
  [Field k]
  {i : Fin (n + 1)} :
-- imply
  Function.Surjective (AffineParts.dehomogenize k i) := by
-- proof
  intro f
  use (rename i.succAbove : MvPolynomial (Fin n) k →ₐ[k] _) f
  have key : (AffineParts.dehomogenize k i).comp
    ((rename i.succAbove : MvPolynomial (Fin n) k →ₐ[k] _).toRingHom) =
    RingHom.id _ := by
    apply ringHom_ext
    · intro a; simp [AffineParts.dehomogenize]
    · intro j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_X, AffineParts.dehomogenize, eval₂Hom_X', Fin.insertNth_apply_succAbove,
        RingHom.id_apply]
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingHom.id_apply] at this
  exact this

end Theorem1324

namespace Corollary1326

/--
[krullDim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma krullDim_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {V V' : Set (Fin n → k)}
-- given
  (hVV' : V = V') :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) = ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') :=
-- proof
  ringKrullDim_eq_of_ringEquiv (coordinateRingEquiv k V V' hVV')

end Corollary1326

namespace Corollary1326

/--
[krullDim_eq_of_projective_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma krullDim_eq_of_projective_closure
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin n) k)} :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) = ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ f ∈ I, eval P f = 0}) :=
-- proof
  krullDim_eq k _ _ (Theorem1323.projective_closure_cap_affine_eq k I)

end Corollary1326

namespace Corollary1326

/--
[krullDim_eq_of_affinePart](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma krullDim_eq_of_affinePart
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)} :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) = ringKrullDim (MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}) :=
-- proof
  krullDim_eq k _ _ (affinePart_eq_dehomogenizedIdeal_zeroLocus k I)

end Corollary1326

namespace Corollary1326

/--
[corollary_13_26_part2_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma corollary_13_26_part2_dimension
  {n : ℕ}
  {k : Type*}
  [Field k]
  {m : ℕ}
  {f : Fin m → MvPolynomial (Fin (n + 1)) k}
  {d : ℕ}
  {i : Fin (n + 1)}
-- given
  (hd : ProjectiveDimension.HasProjectiveDimension k f d) :
-- imply
  ∀ (d_i : ℕ), ProjectiveDimension.HasAffineDimension k n (ProjectiveDimension.affinePartZeroLocusAlgClosed k f i) d_i → d_i ≤ d :=
-- proof
  fun d_i hdi => hd.1 i d_i hdi

end Corollary1326

namespace Corollary1326

/--
[corollary_13_26](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
lemma corollary_13_26
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I₁ : Ideal (MvPolynomial (Fin n) k)}
  {I₂ : Ideal (MvPolynomial (Fin (n + 1)) k)} :
-- imply
  (Nonempty ((MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal I₁, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) ≃+* (MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ f ∈ I₁, eval P f = 0}))) ∧ (Nonempty ((MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ f ∈ I₂, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) ≃+* (MvPolynomial (Fin n) k ⧸ vanishingIdeal k {P : Fin n → k | ∀ g ∈ I₂.map (AffineParts.dehomogenize k 0), eval P g = 0}))) :=
-- proof
  ⟨⟨coordinateRingEquiv_of_projective_closure k I₁⟩,
    ⟨coordinateRingEquiv_of_affinePart k I₂⟩⟩
end Corollary1326
end


/--
[isHomogeneous_eval_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
private lemma isHomogeneous_eval_smul_eq
  [CommSemiring R]
  {f : MvPolynomial σ R}
  {d : ℕ}
  {c : R}
  {x : σ → R}
-- given
  (hf : f.IsHomogeneous d) :
-- imply
  eval (fun i => c * x i) f = c ^ d * eval x f := by
-- proof
  apply HomogeneousPolynomial.isHomogeneous_eval_smul f d hf c x

/--
[mem_affinePatch_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
private lemma mem_affinePatch_mk_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {i : Fin (n + 1)}
  {v : Fin (n + 1) → k}
-- given
  (hv : v ≠ 0) :
-- imply
  Projectivization.mk k v hv ∈ affinePatch k i ↔ v i ≠ 0 := by
-- proof
  apply AffinePatch.mem_affinePatch_mk k i v hv

/--
[mem_affinePatch_iff_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
private lemma mem_affinePatch_iff_rep_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {i : Fin (n + 1)}
  {p : ℙ k (Fin (n + 1) → k)} :
-- imply
  p ∈ affinePatch k i ↔ p.rep i ≠ 0 := by
-- proof
  apply AffinePatch.mem_affinePatch_iff_rep k i p

/--
[insertNth_one_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
private lemma insertNth_one_ne_zero_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {i : Fin (n + 1)}
  {a : Fin n → k} :
-- imply
  i.insertNth (α := fun _ => k) (1 : k) a ≠ 0 := by
-- proof
  apply AffinePatch.insertNth_one_ne_zero k i a

/--
[projective_closure_of_affinePart_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
private lemma projective_closure_of_affinePart_eq_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)} :
-- imply
  {P : Fin n → k | ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} = {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal (I.map (AffineParts.dehomogenize k 0)), eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0} := by
-- proof
  apply Theorem1324.projective_closure_of_affinePart_eq k I

/--
[vanishingIdeal_eq_of_set_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
private lemma vanishingIdeal_eq_of_set_eq_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {S T : Set (Fin n → k)}
-- given
  (h : S = T) :
-- imply
  vanishingIdeal k S = vanishingIdeal k T := by
-- proof
  apply Corollary1326.vanishingIdeal_eq_of_set_eq k S T h

/--
[affinePart_eq_dehomogenizedIdeal_zeroLocus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean)
-/
@[path]
private lemma affinePart_eq_dehomogenizedIdeal_zeroLocus_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {I : Ideal (MvPolynomial (Fin (n + 1)) k)} :
-- imply
  {P : Fin n → k | ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} = {P : Fin n → k | ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0} := by
-- proof
  apply Corollary1326.affinePart_eq_dehomogenizedIdeal_zeroLocus k I


-- created on 2026-10-23
