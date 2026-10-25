import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.KrullDimensionAffineSpace
open Ideal


/--
[ringKrullDim_mvPolynomial_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KrullDimensionAffineSpace.lean)
-/
@[path]
lemma ringKrullDim_mvPolynomial_field
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k) = n := by
-- proof
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/--
[dim_eq_of_ringEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KrullDimensionAffineSpace.lean)
-/
@[path]
lemma dim_eq_of_ringEquiv
  [CommSemiring R]
  [CommSemiring S]
  {e : R ≃+* S} :
-- imply
  ringKrullDim R = ringKrullDim S :=
-- proof
  ringKrullDim_eq_of_ringEquiv e

/--
[PrimeSpectrum.zeroLocus_prime_eq_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KrullDimensionAffineSpace.lean)
-/
@[path]
lemma PrimeSpectrum.zeroLocus_prime_eq_Ici
  [CommRing R]
  {p : Ideal R}
  [p.IsPrime] :
-- imply
  PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
-- proof
  ext q
  simp [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
  rfl

/--
[ringKrullDim_quotient_prime_eq_coheight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KrullDimensionAffineSpace.lean)
-/
@[path]
lemma ringKrullDim_quotient_prime_eq_coheight
  [CommRing R]
  {p : Ideal R}
  [p.IsPrime] :
-- imply
  ringKrullDim (R ⧸ p) = ↑(Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R)) := by
-- proof
  rw [Order.coheight_eq_krullDim_Ici, ← PrimeSpectrum.zeroLocus_prime_eq_Ici]
  exact Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p)

/--
[height_add_ringKrullDim_quotient_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KrullDimensionAffineSpace.lean)
-/
@[path]
lemma height_add_ringKrullDim_quotient_le
  [CommRing R]
  {p : Ideal R}
  [p.IsPrime]
  [Nontrivial R] :
-- imply
  ↑p.height + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
-- proof
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  rw [Ideal.height_eq_primeHeight, ringKrullDim_quotient_prime_eq_coheight]
  change ↑(Ideal.primeHeight p) + ↑(Order.coheight P) ≤ ringKrullDim R
  rw [show (Ideal.primeHeight p : WithBot ℕ∞) = ↑(Order.height P) from rfl]
  rw [← WithBot.coe_add]
  unfold ringKrullDim
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum R)]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) P)


-- created on 2026-10-23
