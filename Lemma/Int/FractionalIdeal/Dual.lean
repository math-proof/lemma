import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.FractionalIdeal.Dual.Part2
open scoped nonZeroDivisors
open Module


/--
[dualSubmodule_mul_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean)
-/
@[path]
lemma dualSubmodule_mul_eq_div
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {M : Submodule A K} :
-- imply
  LinearMap.BilinForm.dualSubmodule (LinearMap.mul K K : LinearMap.BilinForm K K) M =
    (1 : Submodule A K) / M := by
-- proof
  ext x
  simp only [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_div_iff_forall_mul_mem,
    LinearMap.mul_apply']

/--
[Submodule.dualEquivMulDualSubmodule_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean)
-/
@[path]
lemma Submodule.dualEquivMulDualSubmodule_spec
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {M : Submodule A K}
  {f : Module.Dual A M}
  {m : M}
-- given
  (hM : M ≠ ⊥) :
-- imply
  algebraMap A K (f m) = (Submodule.dualEquivMulDualSubmodule M hM f : K) * (m : K) := by
-- proof
  have hfun : LinearMap.BilinForm.dualSubmoduleToDual
    (LinearMap.mul K K : LinearMap.BilinForm K K) M
    (Submodule.dualEquivMulDualSubmodule M hM f) = f :=
    LinearEquiv.symm_apply_apply (Submodule.dualEquivMulDualSubmodule M hM) f
  have hcon := congrArg (fun g : Module.Dual A M => g m) hfun
  have hmap := congrArg (algebraMap A K) hcon
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    LinearMap.BilinForm.dualSubmoduleParing_spec] at hmap
  exact hmap.symm

/--
[Submodule.exists_mul_rep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean)
-/
@[path]
private lemma Submodule_exists_mul_rep_eq
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {M : Submodule A K}
  {f : Module.Dual A M}
-- given
  (hM : M ≠ ⊥) :
-- imply
  ∃ x : K, ∀ m : M, algebraMap A K (f m) = x * m := by
-- proof
  apply Submodule.exists_mul_rep M hM f

/--
[LinearMap.BilinForm.mul_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean)
-/
@[path]
private lemma LinearMap_BilinForm_mul_nondegenerate_eq
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] :
-- imply
  (LinearMap.mul K K : LinearMap.BilinForm K K).Nondegenerate := by
-- proof
  apply LinearMap.BilinForm.mul_nondegenerate

/--
[Submodule.span_coe_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean)
-/
@[path]
private lemma Submodule_span_coe_eq_top_eq
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {M : Submodule A K}
-- given
  (hM : M ≠ ⊥) :
-- imply
  Submodule.span K (M : Set K) = ⊤ := by
-- proof
  apply Submodule.span_coe_eq_top M hM

/--
[Submodule.mul_dualSubmoduleToDual_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean)
-/
@[path]
private lemma Submodule_mul_dualSubmoduleToDual_surjective_eq
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {M : Submodule A K}
-- given
  (hM : M ≠ ⊥) :
-- imply
  Function.Surjective (LinearMap.BilinForm.dualSubmoduleToDual
    (LinearMap.mul K K : LinearMap.BilinForm K K) M) := by
-- proof
  apply Submodule.mul_dualSubmoduleToDual_surjective M hM

/--
[FractionalIdeal.coe_inv_eq_mul_dualSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean)
-/
@[path]
private lemma FractionalIdeal_coe_inv_eq_mul_dualSubmodule_eq
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {I : FractionalIdeal A⁰ K}
-- given
  (hI : I ≠ 0) :
-- imply
  ((I⁻¹ : FractionalIdeal A⁰ K) : Submodule A K) =
    LinearMap.BilinForm.dualSubmodule
    (LinearMap.mul K K : LinearMap.BilinForm K K)
    (I : Submodule A K) := by
-- proof
  apply FractionalIdeal.coe_inv_eq_mul_dualSubmodule I hI


-- created on 2026-10-20
-- updated on 2026-10-26
