import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
open Polynomial


/--
[finrank_quotient_polynomial_eq_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma finrank_quotient_polynomial_eq_natDegree
  {k : Type*}
  [Field k]
  {f : Polynomial k} :
-- imply
  Module.finrank k (Polynomial k ⧸ Ideal.span {f}) = f.natDegree :=
-- proof
  finrank_quotient_span_eq_natDegree

/--
[finrank_quotient_X](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma finrank_quotient_X
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank k (Polynomial k ⧸ Ideal.span {(X : Polynomial k)}) = 1 := by
-- proof
  rw [finrank_quotient_span_eq_natDegree, natDegree_X]

/--
[finrank_quotient_X_sub_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma finrank_quotient_X_sub_C
  {k : Type*}
  [Field k]
  {c : k} :
-- imply
  Module.finrank k (Polynomial k ⧸ Ideal.span {(X : Polynomial k) - C c}) = 1 := by
-- proof
  rw [finrank_quotient_span_eq_natDegree, natDegree_X_sub_C]

/--
[line_line_intersection_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma line_line_intersection_dim
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {Polynomial.C (X : Polynomial k), (X : Polynomial (Polynomial k))}) = 1 := by
-- proof
  have hgens : (Ideal.span {Polynomial.C (X : Polynomial k),
    (X : Polynomial (Polynomial k))} : Ideal (Polynomial (Polynomial k))) =
    Ideal.span {Polynomial.C (X - C (0 : k)),
      (X : Polynomial (Polynomial k)) - C (0 : Polynomial k)} := by simp
  have e := @Polynomial.quotientSpanCXSubCXSubCAlgEquiv k _ (0 : k) (0 : Polynomial k)
  rw [show (1 : ℕ) = Module.finrank k k from (Module.finrank_self k).symm]
  exact LinearEquiv.finrank_eq ((Ideal.quotientEquivAlgOfEq k hgens).trans e).toLinearEquiv

/--
[line_conic_intersection_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma line_conic_intersection_dim
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {Polynomial.C ((X : Polynomial k)^2 + 1), (X : Polynomial (Polynomial k))}) = 2 := by
-- proof
  have e := lineConicQuotientEquiv k
  rw [LinearEquiv.finrank_eq ((e.restrictScalars k).toLinearEquiv)]
  rw [finrank_quotient_span_eq_natDegree]
  compute_degree!

/--
[finrank_quotient_coprime_product](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma finrank_quotient_coprime_product
  {k : Type*}
  [Field k]
  {f g : Polynomial k}
-- given
  (hf : f ≠ 0)
  (hg : g ≠ 0) :
-- imply
  Module.finrank k (Polynomial k ⧸ Ideal.span {f * g}) = f.natDegree + g.natDegree := by
-- proof
  rw [finrank_quotient_span_eq_natDegree, Polynomial.natDegree_mul hf hg]

/--
[finrank_quotient_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma finrank_quotient_algebraMap
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Module.Basis ι (Polynomial k) S}
  {p : Polynomial k}
-- given
  (hp : algebraMap (Polynomial k) S p ≠ 0) :
-- imply
  Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) = Fintype.card ι * p.natDegree := by
-- proof
  rw [finrank_quotient_span_eq_natDegree_norm b hp,
    Algebra.norm_algebraMap_of_basis b,
    Polynomial.natDegree_pow]

/--
[principal_divisor_degree_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma principal_divisor_degree_one
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Module.Basis ι (Polynomial k) S}
  {c : k} :
-- imply
  Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c)}) = Fintype.card ι := by
-- proof
  have hp : algebraMap (Polynomial k) S (X - C c) ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap (Polynomial k) S) :=
      Module.Basis.algebraMap_injective b
    have := hinj (h.trans (map_zero _).symm)
    have : (X - C c : Polynomial k) ≠ 0 := by
      intro heq; have := congr_arg natDegree heq; simp at this
    contradiction
  rw [finrank_quotient_algebraMap k b _ hp, natDegree_X_sub_C, mul_one]

/--
[quotient_polynomial_module_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma quotient_polynomial_module_finite
  {R : Type*}
  [CommRing R]
  {g : Polynomial R}
-- given
  (hg : g.Monic) :
-- imply
  Module.Finite R (Polynomial R ⧸ Ideal.span {g}) :=
-- proof
  hg.finite_adjoinRoot

/--
[bezout_algebraic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_algebraic
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  [IsDomain (AdjoinRoot g)]
  {f : Polynomial k}
-- given
  (hg : g.Monic)
  (hf : algebraMap (Polynomial k) (AdjoinRoot g) f ≠ 0) :
-- imply
  Module.finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f}) = g.natDegree * f.natDegree := by
-- proof
  have b := (AdjoinRoot.powerBasis' hg).basis
  rw [finrank_quotient_span_eq_natDegree_norm b hf,
    Algebra.norm_algebraMap_of_basis b,
    Polynomial.natDegree_pow,
    Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

/--
[bezout_bivariate_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_bivariate_norm
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  [IsDomain (AdjoinRoot g)]
  {f : Polynomial (Polynomial k)}
-- given
  (hg : g.Monic)
  (hf : AdjoinRoot.mk g f ≠ 0) :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ (Ideal.span {g} ⊔ Ideal.span {f})) = (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree := by
-- proof
  rw [LinearEquiv.finrank_eq (bivariate_quotient_equiv k f g).toLinearEquiv]
  exact finrank_quotient_span_eq_natDegree_norm (AdjoinRoot.powerBasis' hg).basis hf

/--
[bezout_bivariate_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_bivariate_base
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  [IsDomain (AdjoinRoot g)]
  {p : Polynomial k}
-- given
  (hg : g.Monic)
  (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ (Ideal.span {g} ⊔ Ideal.span {Polynomial.C p})) = g.natDegree * p.natDegree := by
-- proof
  have hmk : AdjoinRoot.mk g (Polynomial.C p) = algebraMap (Polynomial k) (AdjoinRoot g) p := rfl
  have hf : AdjoinRoot.mk g (Polynomial.C p) ≠ 0 := hmk ▸ hp
  rw [bezout_bivariate_norm k g hg (Polynomial.C p) hf, hmk]
  have b := (AdjoinRoot.powerBasis' hg).basis
  rw [Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
    Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

/--
[bezout_algebraic_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_algebraic_irreducible
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {f : Polynomial k}
-- given
  (hg : g.Monic)
  (hirr : Irreducible g)
  (hf : algebraMap (Polynomial k) (AdjoinRoot g) f ≠ 0) :
-- imply
  Module.finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f}) = g.natDegree * f.natDegree := by
-- proof
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  exact bezout_algebraic k g hg f hf

/--
[ideal_span_pair_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma ideal_span_pair_eq_sup
  [Semiring R]
  {a b : R} :
-- imply
  (Ideal.span {a, b} : Ideal R) = Ideal.span {a} ⊔ Ideal.span {b} := by
-- proof
  rw [← Ideal.span_insert]

/--
[bezout_bivariate_product](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_bivariate_product
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {p : Polynomial k}
-- given
  (hg : g.Monic)
  (hirr : Irreducible g)
  (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g, Polynomial.C p}) = g.natDegree * p.natDegree := by
-- proof
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  rw [ideal_span_pair_eq_sup]
  exact bezout_bivariate_base k g hg p hp

/--
[bezout_bivariate_norm_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_bivariate_norm_irreducible
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {f : Polynomial (Polynomial k)}
-- given
  (hg : g.Monic)
  (hirr : Irreducible g)
  (hf : AdjoinRoot.mk g f ≠ 0) :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g, f}) = (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree := by
-- proof
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  rw [ideal_span_pair_eq_sup]
  exact bezout_bivariate_norm k g hg f hf

/--
[bezout_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_full
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {f : Polynomial (Polynomial k)}
  {n : ℕ}
-- given
  (hg : g.Monic)
  (hirr : Irreducible g)
  (hf : AdjoinRoot.mk g f ≠ 0)
  (hnorm : (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree = n) :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g, f}) = n := by
-- proof
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  calc Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g, f})
    = Module.finrank k (Polynomial (Polynomial k) ⧸
      (Ideal.span {g} ⊔ Ideal.span {f})) :=
      LinearEquiv.finrank_eq (Ideal.quotientEquivAlgOfEq k (ideal_span_pair_eq_sup g f)).toLinearEquiv
    _ = Module.finrank k (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g f}) :=
      LinearEquiv.finrank_eq (bivariate_quotient_equiv k f g).toLinearEquiv
    _ = (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree :=
      finrank_quotient_span_eq_natDegree_norm (AdjoinRoot.powerBasis' hg).basis hf
    _ = n := hnorm

/--
[bezout_norm_degree_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma bezout_norm_degree_base
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {p : Polynomial k}
-- given
  (hg : g.Monic) :
-- imply
  (Algebra.norm (Polynomial k) (AdjoinRoot.mk g (Polynomial.C p))).natDegree = g.natDegree * p.natDegree := by
-- proof
  have hmk : AdjoinRoot.mk g (Polynomial.C p) = algebraMap (Polynomial k) (AdjoinRoot g) p := rfl
  rw [hmk, Algebra.norm_algebraMap_of_basis (AdjoinRoot.powerBasis' hg).basis,
    Polynomial.natDegree_pow, Fintype.card_fin, AdjoinRoot.powerBasis'_dim]

/--
[conic_conic_intersection_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutTheorem.lean)
-/
@[path]
lemma conic_conic_intersection_dim
  {k : Type*}
  [Field k]
  [IsDomain (AdjoinRoot ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k)))]
-- given
  (hne : algebraMap (Polynomial k) (AdjoinRoot ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k))) ((X : Polynomial k)^2 + 1) ≠ 0) :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {(X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k), C ((X : Polynomial k)^2 + 1)}) = 4 := by
-- proof
  rw [ideal_span_pair_eq_sup]
  have hg : ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k)).Monic :=
    monic_X_pow_add_C _ (by norm_num)
  rw [bezout_bivariate_base k _ hg _ hne]
  have h1 : natDegree ((X : Polynomial (Polynomial k))^2 + C (1 : Polynomial k)) = 2 := by
    compute_degree!
  have h2 : natDegree ((X : Polynomial k)^2 + 1) = 2 := by compute_degree!
  rw [h1, h2]


-- created on 2026-10-23
