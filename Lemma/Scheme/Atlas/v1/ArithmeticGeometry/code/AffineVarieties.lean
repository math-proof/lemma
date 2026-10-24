import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.AffineVarieties
open Definition1213 Lemma1214
open MvPolynomial


/--
[weak_nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma weak_nullstellensatz
  {k : Type*}
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (hI : I ≠ ⊤) :
-- imply
  Set.Nonempty (AlgebraicSet k n (I : Set _)) := by
-- proof
  rw [algebraicSet_ideal_eq_zeroLocus]
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hvan : MvPolynomial.vanishingIdeal (AlgebraicClosure k)
    (MvPolynomial.zeroLocus (AlgebraicClosure k) I) = ⊤ := by
    rw [h, MvPolynomial.vanishingIdeal_empty]
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I] at hvan
  exact hI (Ideal.radical_eq_top.mp hvan)
namespace Definition1213
variable {R : Type*} [CommRing R] (I : Ideal R)

namespace Definition1213

/--
[radical_eq_setOf_pow_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma radical_eq_setOf_pow_mem
  {k : Type*}
  [Field k]
  [CommRing R]
  {I : Ideal R} :
-- imply
  (I.radical : Set R) = {x : R | ∃ r : ℕ, 0 < r ∧ x ^ r ∈ I} := by
-- proof
  ext x
  simp only [SetLike.mem_coe, Ideal.mem_radical_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.succ_pos n, by rw [pow_succ]; exact I.mul_mem_right x hn⟩
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr⟩
end Definition1213
namespace Lemma1214

end Definition1213

namespace Lemma1214

/--
[radical_is_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma radical_is_ideal
  {k : Type*}
  [Field k]
  [CommRing R]
  {I : Ideal R} :
-- imply
  ∃ J : Ideal R, (J : Set R) = {x : R | ∃ n : ℕ, x ^ n ∈ I} :=
-- proof
  ⟨I.radical, rfl⟩

end Lemma1214

/--
[algebraicSet_isAlgebraicSubset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma algebraicSet_isAlgebraicSubset
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  IsAlgebraicSubset k n (AlgebraicSet k n S) :=
-- proof
  ⟨S, rfl⟩

/--
[IsIrreducibleAlgebraicSet.nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma IsIrreducibleAlgebraicSet.nonempty
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
-- given
  (h : IsIrreducibleAlgebraicSet k n V) :
-- imply
  V.Nonempty :=
-- proof
  h.1
section NoetherianRing

/--
[isNoetherianRing_iff_every_ideal_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma isNoetherianRing_iff_every_ideal_fg
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R] :
-- imply
  IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
-- proof
  isNoetherianRing_iff_ideal_fg R

/--
[isNoetherianRing_iff_ideal_acc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma isNoetherianRing_iff_ideal_acc
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R] :
-- imply
  IsNoetherianRing R ↔ ∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m := by
-- proof
  rw [isNoetherianRing_iff]
  exact (monotone_stabilizes_iff_noetherian (R := R) (M := R)).symm

/--
[noetherian_fg_iff_acc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma noetherian_fg_iff_acc
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R] :
-- imply
  (∀ I : Ideal R, I.FG) ↔ ∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m := by
-- proof
  rw [← isNoetherianRing_iff_every_ideal_fg, isNoetherianRing_iff_ideal_acc]
end NoetherianRing
section HilbertBasis

/--
[hilbert_basis_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma hilbert_basis_theorem
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [IsNoetherianRing R] :
-- imply
  IsNoetherianRing (Polynomial R) :=
-- proof
  Polynomial.isNoetherianRing
end HilbertBasis
section IdealOfAlgebraicSet
open MvPolynomial
variable {k} {σ : Type*}

/--
[eval_surjective_algebraicClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma eval_surjective_algebraicClosure
  {k : Type*}
  [Field k]
  {n : ℕ}
  {P : Fin n → AlgebraicClosure k} :
-- imply
  Function.Surjective (MvPolynomial.eval P) :=
-- proof
  fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩

/--
[ker_eval_eq_vanishingIdeal_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma ker_eval_eq_vanishingIdeal_singleton
  {k : Type*}
  [Field k]
  {n : ℕ}
  {P : Fin n → AlgebraicClosure k} :
-- imply
  RingHom.ker (MvPolynomial.eval P) = MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} := by
-- proof
  ext f
  simp [RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.aeval_eq_eval]

/--
[vanishingIdeal_singleton_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma vanishingIdeal_singleton_isMaximal
  {k : Type*}
  [Field k]
  {n : ℕ}
  {P : Fin n → AlgebraicClosure k} :
-- imply
  (MvPolynomial.vanishingIdeal (AlgebraicClosure k) ({P} : Set (Fin n → AlgebraicClosure k))).IsMaximal := by
-- proof
  rw [← ker_eval_eq_vanishingIdeal_singleton k P]
  exact RingHom.ker_isMaximal_of_surjective _ (eval_surjective_algebraicClosure k P)

/--
[maximal_ideal_eq_vanishingIdeal_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma maximal_ideal_eq_vanishingIdeal_singleton
  {k : Type*}
  [Field k]
  {n : ℕ}
  {m : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (hm : m.IsMaximal) :
-- imply
  ∃ P : Fin n → AlgebraicClosure k, m = MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} := by
-- proof
  have hZ_nonempty : Set.Nonempty (MvPolynomial.zeroLocus (AlgebraicClosure k) m) := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : MvPolynomial.vanishingIdeal (AlgebraicClosure k)
      (MvPolynomial.zeroLocus (AlgebraicClosure k) m) = ⊤ := by
      rw [h, MvPolynomial.vanishingIdeal_empty]
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at this
    exact hm.ne_top (Ideal.radical_eq_top.mp this)
  obtain ⟨P, hP⟩ := hZ_nonempty
  use P
  have h1 : m ≤ MvPolynomial.vanishingIdeal (AlgebraicClosure k)
    (MvPolynomial.zeroLocus (AlgebraicClosure k) m) :=
    MvPolynomial.le_vanishingIdeal_zeroLocus m
  have h2 : MvPolynomial.vanishingIdeal (AlgebraicClosure k)
    (MvPolynomial.zeroLocus (AlgebraicClosure k) m) ≤
    MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} :=
    MvPolynomial.vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hP)
  haveI : (MvPolynomial.vanishingIdeal (AlgebraicClosure k)
    ({P} : Set (Fin n → AlgebraicClosure k))).IsMaximal :=
    vanishingIdeal_singleton_isMaximal k P
  exact hm.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) (le_trans h1 h2)

/--
[corollary_12_17](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma corollary_12_17
  {k : Type*}
  [Field k]
  {n : ℕ}
  {m : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  m.IsMaximal ↔ ∃ P : Fin n → AlgebraicClosure k, m = MvPolynomial.vanishingIdeal (AlgebraicClosure k) {P} := by
-- proof
  constructor
  · exact maximal_ideal_eq_vanishingIdeal_singleton k m
  · rintro ⟨P, rfl⟩
    exact vanishingIdeal_singleton_isMaximal k P
section AffineCoordinateRings
open MvPolynomial
variable {k}

/--
[mem_idealOverK_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
lemma mem_idealOverK_iff
  {k : Type*}
  [Field k]
  {k}
  {n : ℕ}
  {Z : Set (Fin n → AlgebraicClosure k)}
  {f : MvPolynomial (Fin n) k} :
-- imply
  f ∈ idealOverK Z ↔ MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f ∈ idealOfAlgebraicSet Z := by
-- proof
  rfl

/--
[eval_eq_aeval_algebraicClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma eval_eq_aeval_algebraicClosure_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {P : AffineSpace_k k n}
  {f : MvPolynomial (Fin n) (AlgebraicClosure k)} :
-- imply
  MvPolynomial.eval P f = MvPolynomial.aeval P f := by
-- proof
  apply eval_eq_aeval_algebraicClosure k P f

/--
[algebraicSet_ideal_eq_zeroLocus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma algebraicSet_ideal_eq_zeroLocus_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  AlgebraicSet k n (I : Set _) = MvPolynomial.zeroLocus (AlgebraicClosure k) I := by
-- proof
  apply algebraicSet_ideal_eq_zeroLocus k I

/--
[mem_idealOfAlgebraicSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma mem_idealOfAlgebraicSet_iff_eq
  {k : Type*}
  [Field k]
  {k}
  {Z : Set (σ → k)}
  {f : MvPolynomial σ k} :
-- imply
  f ∈ idealOfAlgebraicSet Z ↔ ∀ P ∈ Z, MvPolynomial.eval P f = 0 := by
-- proof
  apply mem_idealOfAlgebraicSet_iff k

/--
[idealOfAlgebraicSet_eq_vanishingIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma idealOfAlgebraicSet_eq_vanishingIdeal_eq
  {k : Type*}
  [Field k]
  {k}
  {Z : Set (σ → k)} :
-- imply
  idealOfAlgebraicSet Z = MvPolynomial.vanishingIdeal k Z := by
-- proof
  apply idealOfAlgebraicSet_eq_vanishingIdeal k Z

/--
[idealOfAlgebraicSet_anti_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma idealOfAlgebraicSet_anti_mono_eq
  {k : Type*}
  [Field k]
  {k}
  {Y Z : Set (σ → k)}
-- given
  (h : Y ⊆ Z) :
-- imply
  idealOfAlgebraicSet Z ≤ idealOfAlgebraicSet Y := by
-- proof
  apply idealOfAlgebraicSet_anti_mono k h

/--
[idealOfAlgebraicSet_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma idealOfAlgebraicSet_union_eq
  {k : Type*}
  [Field k]
  {k}
  {Y Z : Set (σ → k)} :
-- imply
  idealOfAlgebraicSet (Y ∪ Z) = idealOfAlgebraicSet Y ⊓ idealOfAlgebraicSet Z := by
-- proof
  apply idealOfAlgebraicSet_union k Y Z

/--
[hilbert_nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma hilbert_nullstellensatz_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  idealOfAlgebraicSet (AlgebraicSet k n (I : Set _)) = I.radical := by
-- proof
  apply hilbert_nullstellensatz k I

/--
[algebraicSet_idealOfAlgebraicSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma algebraicSet_idealOfAlgebraicSet_eq_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  AlgebraicSet k n ((idealOfAlgebraicSet (AlgebraicSet k n S)) : Set _) = AlgebraicSet k n S := by
-- proof
  apply algebraicSet_idealOfAlgebraicSet_eq k S

/--
[algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
-- given
  (hV : IsAlgebraicSubset k n V) :
-- imply
  AlgebraicSet k n ((idealOfAlgebraicSet V) : Set _) = V := by
-- proof
  apply algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV

/--
[isIrreducibleAlgebraicSet_iff_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma isIrreducibleAlgebraicSet_iff_isPrime_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
-- given
  (hV : IsAlgebraicSubset k n V) :
-- imply
  IsIrreducibleAlgebraicSet k n V ↔ (idealOfAlgebraicSet V).IsPrime := by
-- proof
  apply isIrreducibleAlgebraicSet_iff_isPrime k hV

/--
[idealOfAlgebraicSet_isRadical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma idealOfAlgebraicSet_isRadical_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)} :
-- imply
  (idealOfAlgebraicSet V).IsRadical := by
-- proof
  apply idealOfAlgebraicSet_isRadical k V

/--
[idealOfAlgebraicSet_algebraicSet_of_isRadical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean)
-/
@[path]
private lemma idealOfAlgebraicSet_algebraicSet_of_isRadical_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))}
-- given
  (hI : I.IsRadical) :
-- imply
  idealOfAlgebraicSet (AlgebraicSet k n (I : Set _)) = I := by
-- proof
  apply idealOfAlgebraicSet_algebraicSet_of_isRadical k I hI


-- created on 2026-10-23
