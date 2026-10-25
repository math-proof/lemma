import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
open Finset FusionRing FusionRing.GrRingOf repZ2
open FusionRing


namespace FusionRing

/--
[unit_mul_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma unit_mul_int
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {j k : ι} :
-- imply
  (R.N R.unit j k : ℤ) = if j = k then 1 else 0 := by
-- proof
  rw [R.unit_mul]; split <;> simp

end FusionRing

namespace FusionRing

/--
[mul_unit_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma mul_unit_int
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i k : ι} :
-- imply
  (R.N i R.unit k : ℤ) = if i = k then 1 else 0 := by
-- proof
  rw [R.mul_unit]; split <;> simp

end FusionRing

namespace FusionRing

/--
[assoc_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma assoc_int
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j k l : ι} :
-- imply
  (univ.sum fun m => (R.N i j m : ℤ) * (R.N m k l : ℤ)) = (univ.sum fun m => (R.N j k m : ℤ) * (R.N i m l : ℤ)) := by
-- proof
  exact_mod_cast R.assoc i j k l

end FusionRing

namespace FusionRing

/--
[sum_ite_const_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma sum_ite_const_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  [AddCommMonoid α]
  {p : Prop}
  [Decidable p]
  {s : Finset ι'}
  {f : ι' → α} :
-- imply
  (∑ x ∈ s, if p then f x else 0) = if p then ∑ x ∈ s, f x else 0 := by
-- proof
  split <;> simp_all

end FusionRing

namespace FusionRing

/--
[grMul_one_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grMul_one_left
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : GrRing ι} :
-- imply
  R.grMul R.grOne f = f := by
-- proof
  funext k; unfold grMul grOne
  simp_rw [ite_mul, one_mul, zero_mul, sum_ite_const_zero,
    sum_ite_eq', mem_univ, if_true, R.unit_mul_int,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

end FusionRing

namespace FusionRing

/--
[grMul_one_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grMul_one_right
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {f : GrRing ι} :
-- imply
  R.grMul f R.grOne = f := by
-- proof
  funext k; unfold grMul grOne
  simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true, R.mul_unit_int,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

end FusionRing

namespace FusionRing

/--
[inner_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma inner_sum_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : GrRing ι}
  {l i j k : ι} :
-- imply
  (∑ m : ι, a i * (b j * (c k * ((R.N i j m : ℤ) * (R.N m k l : ℤ))))) = (∑ q : ι, a i * (b j * (c k * ((R.N j k q : ℤ) * (R.N i q l : ℤ))))) := by
-- proof
  simp_rw [← Finset.mul_sum]
  congr 3
  exact R.assoc_int i j k l

end FusionRing

namespace FusionRing

/--
[grMul_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grMul_assoc
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : GrRing ι} :
-- imply
  R.grMul (R.grMul a b) c = R.grMul a (R.grMul b c) := by
-- proof
  funext l; simp only [grMul]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  trans (∑ i : ι, ∑ j, ∑ k, ∑ m,
    a i * (b j * (c k * ((R.N i j m : ℤ) * (R.N m k l : ℤ)))))
  ·
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k; congr 1; ext m; ring
  ·
    conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k
    exact R.inner_sum_eq a b c l i j k

end FusionRing

namespace FusionRing

/--
[grMul_left_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grMul_left_distrib
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : GrRing ι} :
-- imply
  R.grMul a (fun k => b k + c k) = fun k => R.grMul a b k + R.grMul a c k := by
-- proof
  funext l; simp only [grMul]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

end FusionRing

namespace FusionRing

/--
[grMul_right_distrib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grMul_right_distrib
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : GrRing ι} :
-- imply
  R.grMul (fun k => a k + b k) c = fun k => R.grMul a c k + R.grMul b c k := by
-- proof
  funext l; simp only [grMul]
  simp_rw [add_mul, Finset.sum_add_distrib]

end FusionRing

namespace FusionRing

/--
[grMul_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grMul_zero
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a : GrRing ι} :
-- imply
  R.grMul a (fun _ => 0) = fun _ => 0 := by
-- proof
  funext l; simp only [grMul]; simp

end FusionRing

namespace FusionRing

/--
[grZero_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grZero_mul
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a : GrRing ι} :
-- imply
  R.grMul (fun _ => 0) a = fun _ => 0 := by
-- proof
  funext l; simp only [grMul]; simp

end FusionRing

namespace FusionRing

/--
[basisVec_unit_eq_grOne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma basisVec_unit_eq_grOne
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  basisVec R.unit = R.grOne := by
-- proof
  funext k; simp [basisVec, grOne]

end FusionRing

namespace FusionRing

/--
[grothendieckRing_mul_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma grothendieckRing_mul_assoc
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : GrRingOf R} :
-- imply
  a * b * c = a * (b * c) :=
-- proof
  mul_assoc a b c

end FusionRing

namespace FusionRing

/--
[Lemma_1_16_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma Lemma_1_16_1
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {a b c : GrRingOf R} :
-- imply
  a * b * c = a * (b * c) :=
-- proof
  R.grothendieckRing_mul_assoc a b c

end FusionRing

namespace FusionRing

/--
[FusionRingHom.grMap_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma FusionRingHom.grMap_one
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S} :
-- imply
  φ.grMap R.grOne = S.grOne := by
-- proof
  funext l; simp only [grMap, grOne]
  simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact φ.map_unit l

end FusionRing

namespace FusionRing

/--
[FusionRingHom.grMap_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma FusionRingHom.grMap_add
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S}
  {f g : GrRing ι} :
-- imply
  φ.grMap (fun k => f k + g k) = fun l => φ.grMap f l + φ.grMap g l := by
-- proof
  funext l; simp only [grMap]
  simp_rw [add_mul, Finset.sum_add_distrib]

end FusionRing

namespace FusionRing

/--
[FusionRingHom.grMap_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma FusionRingHom.grMap_mul
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S}
  {f g : GrRing ι} :
-- imply
  φ.grMap (R.grMul f g) = S.grMul (φ.grMap f) (φ.grMap g) := by
-- proof
  funext l; simp only [grMap, grMul]
  trans (∑ i : ι, ∑ j : ι, f i * g j *
    (Finset.univ.sum fun k => (R.N i j k : ℤ) * φ.M k l))
  ·
    simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  ·
    simp_rw [φ.map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext p; arg 2; ext q; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
    congr 1; ext p; congr 1; ext q; congr 1; ext i; congr 1; ext j; ring

end FusionRing

namespace repZ2

/--
[mul_e1_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
lemma mul_e1_e1
-- imply
  grMul repZ2 (basisVec 1) (basisVec 1) = basisVec 0 := by
-- proof
  funext k; simp only [grMul, basisVec]
  revert k; decide

end repZ2

/--
[coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
private lemma coeff_zero_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {k : ι} :
-- imply
  (0 : GrRingOf R).coeff k = 0 := by
-- proof
  apply FusionRing.GrRingOf.coeff_zero R k

/--
[coeff_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
private lemma coeff_add_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a b : GrRingOf R}
  {k : ι} :
-- imply
  (a + b).coeff k = a.coeff k + b.coeff k := by
-- proof
  apply FusionRing.GrRingOf.coeff_add R a b k

/--
[coeff_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
private lemma coeff_neg_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a : GrRingOf R}
  {k : ι} :
-- imply
  (-a).coeff k = -a.coeff k := by
-- proof
  apply FusionRing.GrRingOf.coeff_neg R a k

/--
[coeff_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean)
-/
@[path]
private lemma coeff_sub_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {R : FusionRing ι}
  {a b : GrRingOf R}
  {k : ι} :
-- imply
  (a - b).coeff k = a.coeff k - b.coeff k := by
-- proof
  apply FusionRing.GrRingOf.coeff_sub R a b k


-- created on 2026-10-23
