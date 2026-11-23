module

public import Mathlib
public import Theorem.LinearMap.DatumAndHonda
public import Theorem.RingHom.WittVectorHom
public import Theorem.Int.WittHomColimit
public import Theorem.AlgHom.WittGroupHopf
public import Class.HopfAlgebra_HopfIdealQuotient
public import Instance.Dieudonne_WittKernelHopf
public import Notation.Dieudonne_WittKernelHopf

public section

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

omit hp in
@[simp] public theorem coeff_frobeniusFun_iterate (c : ℕ) (x : TruncatedWittVector p n R) (i : Fin n) :
    (frobeniusFun^[c] x).coeff i = x.coeff i ^ p ^ c := by
  induction c generalizing x with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply', coeff_frobeniusFun, ih, ← pow_mul, ← pow_succ]

omit hp in

public theorem frobeniusFun_iterate_mk (c : ℕ) (g : Fin n → R) :
    frobeniusFun^[c] (TruncatedWittVector.mk p g) = TruncatedWittVector.mk p fun i => g i ^ p ^ c :=
  TruncatedWittVector.ext fun i => by
    rw [coeff_frobeniusFun_iterate, TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_mk]


public theorem map_frobeniusFun_iterate (f : R →+* S) (c : ℕ) (x : TruncatedWittVector p n R) :
    map f (frobeniusFun^[c] x) = frobeniusFun^[c] (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, coeff_frobeniusFun_iterate, map_pow]


public theorem frobeniusFun_iterate_add (hR : (p : R) = 0) (c : ℕ) (x y : TruncatedWittVector p n R) :
    frobeniusFun^[c] (x + y) = frobeniusFun^[c] x + frobeniusFun^[c] y := by
  induction c generalizing x y with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, frobeniusFun_add hR]


public theorem frobeniusFun_iterate_zero (c : ℕ) : frobeniusFun^[c] (0 : TruncatedWittVector p n R) = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Function.iterate_succ_apply', ih, frobeniusFun_zero]


public theorem frobeniusFun_iterate_neg (hR : (p : R) = 0) (c : ℕ) (x : TruncatedWittVector p n R) :
    frobeniusFun^[c] (-x) = -frobeniusFun^[c] x := by
  have h := frobeniusFun_iterate_add hR c (-x) x
  rw [neg_add_cancel, frobeniusFun_iterate_zero] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

end TruncWitt

namespace WittKernel

open WittGroup TruncWitt

variable (k : Type u) [CommRing k] (p : ℕ) (n a b : ℕ) (J : Type v)


public theorem relation_mem_ideal (j : J) (i : Fin n) : relation k p n a b J j i ∈ ideal k p n a b J :=
  Ideal.subset_span ⟨(j, i), rfl⟩


public theorem ideal_le_iff {I : Ideal (WittGroup.Coord k p n J)} :
    ideal k p n a b J ≤ I ↔ ∀ j i, relation k p n a b J j i ∈ I := by
  constructor
  · exact fun h j i => h (relation_mem_ideal j i)
  · intro h
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact h j i

variable [hp : Fact p.Prime]


public theorem ringHom_X_pow {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) (j : J)
    (i : Fin n) (c : ℕ) :
    g (X j i) ^ p ^ c = (frobeniusFun^[c] (TruncWitt.map (p := p) g (univ k p n j))).coeff i := by
  rw [coeff_frobeniusFun_iterate, coeff_map, coeff_univ]


public theorem ringHom_relation {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) (j : J)
    (i : Fin n) :
    g (relation k p n a b J j i) =
      (frobeniusFun^[b] (TruncWitt.map (p := p) g (univ k p n j))).coeff i -
        (frobeniusFun^[a] (TruncWitt.map (p := p) g (univ k p n j))).coeff i := by
  rw [relation, map_sub, map_pow, map_pow, ringHom_X_pow, ringHom_X_pow]


public theorem ideal_le_ker_iff {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) :
    ideal k p n a b J ≤ RingHom.ker g ↔
      ∀ j, frobeniusFun^[b] (TruncWitt.map (p := p) g (univ k p n j)) =
        frobeniusFun^[a] (TruncWitt.map (p := p) g (univ k p n j)) := by
  rw [ideal_le_iff]
  simp only [RingHom.mem_ker, ringHom_relation, sub_eq_zero]
  exact ⟨fun h j => TruncatedWittVector.ext fun i => h j i,
    fun h j i => congrArg (TruncatedWittVector.coeff i) (h j)⟩

section HopfIdeal

variable [CharP k p]

variable (k p n a b J)

open scoped Dieudonne_WittKernelHopf

omit [CharP k p] in


public theorem frobeniusFun_iterate_map_mk_univ (j : J) :
    frobeniusFun^[b] (TruncWitt.map (p := p) πI (univ k p n j)) =
      frobeniusFun^[a] (TruncWitt.map (p := p) πI (univ k p n j)) :=
  (ideal_le_ker_iff (πI : 𝒪 →+* 𝒪 ⧸ I)).1 (by rw [Ideal.mk_ker]) j

end HopfIdeal

variable (k p n a b J)


@[simp] public theorem π_apply (x : WittGroup.Coord k p n J) :
    π k p n a b J x = Ideal.Quotient.mk (ideal k p n a b J) x := rfl


public theorem π_toAlgHom :
    (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] Coord k p n a b J) =
      Ideal.Quotient.mkₐ k (ideal k p n a b J) := rfl


public theorem π_surjective : Surjective (π k p n a b J) := Ideal.Quotient.mk_surjective


public theorem π_relation (j : J) (i : Fin n) : π k p n a b J (relation k p n a b J j i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (relation_mem_ideal j i)


public theorem π_X_pow_eq (j : J) (i : Fin n) :
    π k p n a b J (X j i) ^ p ^ b = π k p n a b J (X j i) ^ p ^ a := by
  rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub]
  exact π_relation j i


public theorem adjoin_range_π_X_eq_top :
    Algebra.adjoin k (Set.range fun ji : J × Fin n => π k p n a b J (X ji.1 ji.2)) = ⊤ := by
  have h1 : (Set.range fun ji : J × Fin n => π k p n a b J (X ji.1 ji.2)) =
      (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] Coord k p n a b J) ''
        Set.range (fun ji : J × Fin n => (MvPolynomial.X ji : MvPolynomial (J × Fin n) k)) := by
    rw [← Set.range_comp]
    rfl
  rw [h1, Algebra.adjoin_image]
  have h2 : Algebra.adjoin k (Set.range fun ji : J × Fin n =>
      (MvPolynomial.X ji : MvPolynomial (J × Fin n) k)) = ⊤ := MvPolynomial.adjoin_range_X
  change Subalgebra.map _ (Algebra.adjoin k (Set.range fun ji : J × Fin n =>
      (MvPolynomial.X ji : MvPolynomial (J × Fin n) k))) = ⊤
  rw [h2, Algebra.map_top, AlgHom.range_eq_top]
  exact π_surjective


public theorem isIntegral_π_X (hab : a < b) (j : J) (i : Fin n) : IsIntegral k (π k p n a b J (X j i)) := by
  have hlt : p ^ a < p ^ b := Nat.pow_lt_pow_right hp.out.one_lt hab
  refine ⟨Polynomial.X ^ p ^ b - Polynomial.X ^ p ^ a, ?_, ?_⟩
  · refine Polynomial.monic_X_pow_sub (lt_of_le_of_lt (Polynomial.degree_X_pow_le _) ?_)
    exact_mod_cast hlt
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X_pow]
    rw [sub_eq_zero]
    exact π_X_pow_eq j i


public theorem moduleFinite [Finite J] (hab : a < b) : Module.Finite k (Coord k p n a b J) := by
  have hfg := fg_adjoin_of_finite (R := k)
    (s := Set.range fun ji : J × Fin n => π k p n a b J (X ji.1 ji.2)) (Set.finite_range _)
    (fun x hx => by
      obtain ⟨⟨j, i⟩, rfl⟩ := hx
      exact isIntegral_π_X hab j i)
  rw [adjoin_range_π_X_eq_top, Algebra.top_toSubmodule] at hfg
  exact Module.Finite.of_fg_top hfg

variable (k p n a b J)


@[simp] public theorem coe_tauto (j : J) :
    (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)) =
      TruncWitt.map (p := p) (Ideal.Quotient.mk (ideal k p n a b J)) (univ k p n j) := rfl


@[simp] public theorem coeff_tauto (j : J) (i : Fin n) :
    (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)).coeff i =
      π k p n a b J (X j i) := by
  rw [coe_tauto, coeff_map, coeff_univ, π_apply]


public theorem frobenius_iterate_tauto (j : J) :
    (wittHomFrobenius k p n (Coord k p n a b J))^[b] (tauto k p n a b J j) =
      (wittHomFrobenius k p n (Coord k p n a b J))^[a] (tauto k p n a b J j) := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (((wittHomFrobenius k p n (Coord k p n a b J))^[c] x : wittHom k p n (Coord k p n a b J)) :
        TruncatedWittVector p n (Coord k p n a b J)) = frobeniusFun^[c] (x : TruncatedWittVector p n _) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_wittHomFrobenius, ih]
  apply Subtype.ext
  rw [key, key, coe_tauto]
  exact frobeniusFun_iterate_map_mk_univ k p n a b J j


public theorem verschiebung_iterate_tauto (j : J) :
    (wittHomVerschiebung k p n (Coord k p n a b J))^[n] (tauto k p n a b J j) = 0 :=
  wittHomVerschiebung_iterate_eq_zero _

variable (k p n a b J) in


public theorem tautoClass_def (j : J) :
    tautoClass k p n a b J j = DieudonneModule.of k p (Coord k p n a b J) n (tauto k p n a b J j) :=
  rfl


public theorem frobenius_iterate_tautoClass (j : J) :
    (DieudonneModule.frobenius k p (Coord k p n a b J))^[b] (tautoClass k p n a b J j) =
      (DieudonneModule.frobenius k p (Coord k p n a b J))^[a] (tautoClass k p n a b J j) := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (DieudonneModule.frobenius k p (Coord k p n a b J))^[c] (DieudonneModule.of k p _ n x) =
        DieudonneModule.of k p _ n ((wittHomFrobenius k p n (Coord k p n a b J))^[c] x) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        DieudonneModule.frobenius_of]
  rw [tautoClass_def, key, key, frobenius_iterate_tauto]


public theorem verschiebung_iterate_tautoClass (j : J) :
    (DieudonneModule.verschiebung k p (Coord k p n a b J))^[n] (tautoClass k p n a b J j) = 0 := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (DieudonneModule.verschiebung k p (Coord k p n a b J))^[c] (DieudonneModule.of k p _ n x) =
        DieudonneModule.of k p _ n ((wittHomVerschiebung k p n (Coord k p n a b J))^[c] x) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        DieudonneModule.verschiebung_of]
  rw [tautoClass_def, key, verschiebung_iterate_tauto, map_zero]


public theorem adjoin_coeff_tauto_eq_top :
    Algebra.adjoin k {c : Coord k p n a b J | ∃ (j : J) (i : Fin n),
      (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)).coeff i = c} = ⊤ := by
  refine top_le_iff.1 (le_trans (le_of_eq adjoin_range_π_X_eq_top.symm) (Algebra.adjoin_mono ?_))
  rintro _ ⟨⟨j, i⟩, rfl⟩
  exact ⟨j, i, coeff_tauto j i⟩


public theorem adjoin_coeff_wittHom_eq_top :
    Algebra.adjoin k {c : Coord k p n a b J | ∃ (x : wittHom k p n (Coord k p n a b J)) (i : Fin n),
      (x : TruncatedWittVector p n (Coord k p n a b J)).coeff i = c} = ⊤ := by
  refine top_le_iff.1 (le_trans (le_of_eq adjoin_coeff_tauto_eq_top.symm) (Algebra.adjoin_mono ?_))
  rintro _ ⟨j, i, rfl⟩
  exact ⟨tauto k p n a b J j, i, rfl⟩

section Points

variable {T : Type w} [CommRing T] [Algebra k T]


public theorem pointsEquiv_apply_coeff (f : Coord k p n a b J →ₐ[k] T) (j : J) (i : Fin n) :
    ((pointsEquiv f).1 j).coeff i = f (π k p n a b J (X j i)) := by
  change (WittGroup.pointsEquiv _ j).coeff i = _
  rw [coeff_pointsEquiv]
  rfl

end Points


public theorem π_X_ne_zero [Nontrivial k] (j : J) (i : Fin n) :
    π k p n a b J (X j i) ≠ 0 := by
  classical

  let x : J → TruncatedWittVector p n k := fun j' =>
    TruncatedWittVector.mk p fun i' => if j' = j ∧ i' = i then 1 else 0
  have hx : ∀ j', frobeniusFun^[b] (x j') = frobeniusFun^[a] (x j') := by
    intro j'
    refine TruncatedWittVector.ext fun i' => ?_
    simp only [coeff_frobeniusFun_iterate, x, TruncatedWittVector.coeff_mk]
    split_ifs
    · rw [one_pow, one_pow]
    · rw [zero_pow (pow_ne_zero _ hp.out.ne_zero), zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  let f : Coord k p n a b J →ₐ[k] k := pointsEquiv.symm ⟨x, hx⟩
  intro h
  have h1 : f (π k p n a b J (X j i)) = 1 := by
    rw [← pointsEquiv_apply_coeff, Equiv.apply_symm_apply]
    simp [x]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

end WittKernel

end Deformation
