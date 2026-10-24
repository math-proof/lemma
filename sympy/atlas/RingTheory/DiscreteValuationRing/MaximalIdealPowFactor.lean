/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowFactor.lean -/

/-
Author: Muse Code
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPiece
import Lemma.Int.DiscreteValuationRing.MaximalIdealGradedPiece
/-!
# Residue-field quotients of a DVR extension by maximal-ideal powers

Let `A` and `B` be commutative-domain discrete valuation rings with an
`A`-algebra structure on `B`. For each `n`, this file defines the canonical
quotient of `B` by `map 𝔪A ⊔ 𝔪B ^ n` and equips it with its canonical
`ResidueField A`-algebra structure, together with the canonical factor map
from index `n + 1` to index `n` and its surjectivity.

ATLAS source (item NumberTheoryI N261):
[`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines set up the ramification/different valuations for the corrected
quotient-filtration proof; they state no quotient-tower API.

Source-to-API map: for NumberTheoryI N261, the public declarations
`ResidueFieldMaximalIdealPowQuotient`, `instAlgebraQuot`,
`instAlgebraResidue`, `maximalIdealPowQuotientIdeal_le`,
`factorResidueFieldMaximalIdealPowQuotient`,
`factorResidueFieldMaximalIdealPowQuotient_surjective`,
`factorResidueFieldMaximalIdealPowQuotient_mk`,
`maximalIdealPowQuotientIdeal_eq`,
`residueFieldMaximalIdealPowQuotientEquivPow`,
`residueFieldMaximalIdealPowQuotientEquivPow_mk`,
`residueFieldLinearEquivMaximalIdealGradedPieceKerFactor`, and
`residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk` are new
supporting API for the quotient-filtration route, not declarations present
in the pinned ATLAS lines 1237--1324.

This file is new supporting API (prerequisite infrastructure for the corrected
quotient-filtration proof), not a theorem stated in ATLAS and not the final
different-exponent bound.

## Public declarations

* `ResidueFieldMaximalIdealPowQuotient`: the quotient
  `B ⧸ (map 𝔪A ⊔ 𝔪B ^ n)`.
* `instAlgebraQuot`: the canonical `A ⧸ 𝔪A`-algebra structure, via
  `Ideal.Quotient.algebraQuotientOfLEComap`.
* `instAlgebraResidue`: the `ResidueField A`-algebra structure, transported
  along the definitional unfolding `ResidueField A = A ⧸ 𝔪A`.
* `maximalIdealPowQuotientIdeal_le`: the containment
  `map 𝔪A ⊔ 𝔪B ^ (n + 1) ≤ map 𝔪A ⊔ 𝔪B ^ n`.
* `maximalIdealPowQuotientIdeal_eq`: under `map 𝔪A ≤ 𝔪B ^ n`, the defining
  ideal `map 𝔪A ⊔ 𝔪B ^ n` equals `𝔪B ^ n`.
* `factorResidueFieldMaximalIdealPowQuotient`: the canonical
  `ResidueField A`-algebra factor map from index `n + 1` to index `n`.
* `factorResidueFieldMaximalIdealPowQuotient_surjective`: surjectivity of the
  factor map.
* `factorResidueFieldMaximalIdealPowQuotient_mk`: the factor map fixes
  quotient representatives.
* `residueFieldMaximalIdealPowQuotientEquivPow`: under
  `map 𝔪A ≤ 𝔪B ^ n`, the ring equivalence with `B ⧸ 𝔪B ^ n`.
* `residueFieldMaximalIdealPowQuotientEquivPow_mk`: the equivalence fixes
  quotient representatives.
* `residueFieldLinearEquivMaximalIdealGradedPieceKerFactor`: under
  `map 𝔪A ≤ 𝔪B ^ (n + 1)`, the `ResidueField A`-linear equivalence between
  the `n`-th maximal-ideal graded piece of `B` and the kernel of the factor
  map from index `n + 1` to index `n`.
* `residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk`: the kernel
  equivalence sends a graded representative to the corresponding quotient
  representative.

Deferred to later stages: the trace recurrence, the full quotient trace
formula, the different containment, and the valuation bounds.
-/

open IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]

/-- The canonical quotient of `B` by `map 𝔪A ⊔ 𝔪B ^ n`, where `𝔪A` and `𝔪B`
are the maximal ideals. This is new supporting infrastructure for the
corrected ATLAS N261 quotient-filtration route, not a source theorem. -/
abbrev ResidueFieldMaximalIdealPowQuotient (n : ℕ) : Type _ :=
  B ⧸ (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ n :
    Ideal B)

/-- Canonical `(A ⧸ 𝔪A)`-algebra structure on the quotient, from
`Ideal.Quotient.algebraQuotientOfLEComap` applied to
`Ideal.map_le_iff_le_comap.mp le_sup_left`. -/
instance instAlgebraQuot (n : ℕ) :
    Algebra (A ⧸ maximalIdeal A) (ResidueFieldMaximalIdealPowQuotient A B n) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp le_sup_left)

/-- Residue-field scalar action on the quotient, transported along the
definitional unfolding `ResidueField A = A ⧸ 𝔪A` from the generic
`Algebra (A ⧸ 𝔪A)` instance (typeclass resolution does not unfold the plain
`ResidueField` def on its own). -/
instance instAlgebraResidue (n : ℕ) :
    Algebra (ResidueField A) (ResidueFieldMaximalIdealPowQuotient A B n) :=
  inferInstanceAs (Algebra (A ⧸ maximalIdeal A) _)

/-- Under `map 𝔪A ≤ 𝔪B ^ n`, the defining ideal `map 𝔪A ⊔ 𝔪B ^ n` collapses
to `𝔪B ^ n`, by `sup_eq_right`. -/
theorem maximalIdealPowQuotientIdeal_eq (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
    (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ n :
      Ideal B) = maximalIdeal B ^ n :=
  sup_eq_right.mpr h

/-- The defining ideals shrink with `n`: `map 𝔪A ⊔ 𝔪B ^ (n + 1)` is contained
in `map 𝔪A ⊔ 𝔪B ^ n`, by `Ideal.pow_le_pow_right n.le_succ` and lattice
monotonicity. -/
theorem maximalIdealPowQuotientIdeal_le (n : ℕ) :
    (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ (n + 1) :
      Ideal B) ≤
      Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ n :=
  sup_le_sup le_rfl (Ideal.pow_le_pow_right n.le_succ)

/-- The canonical `ResidueField A`-algebra factor map from index `n + 1` to
index `n`. The underlying ring hom is `Ideal.Quotient.factor` for the
containment `maximalIdealPowQuotientIdeal_le`; scalar compatibility is by
quotient induction on a residue-field representative (both algebra maps send
`⟦a⟧` to `⟦algebraMap A B a⟧`, definitionally). -/
noncomputable def factorResidueFieldMaximalIdealPowQuotient (n : ℕ) :
    ResidueFieldMaximalIdealPowQuotient A B (n + 1) →ₐ[ResidueField A]
      ResidueFieldMaximalIdealPowQuotient A B n :=
  { Ideal.Quotient.factor (maximalIdealPowQuotientIdeal_le A B n) with
    commutes' := fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      rfl }

/-- The canonical factor map fixes quotient representatives, by
`Ideal.Quotient.factor_mk`. -/
@[simp]
theorem factorResidueFieldMaximalIdealPowQuotient_mk (n : ℕ) (b : B) :
    factorResidueFieldMaximalIdealPowQuotient A B n
        (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ b :=
  rfl

/-- Under `map 𝔪A ≤ 𝔪B ^ n`, the quotient by `map 𝔪A ⊔ 𝔪B ^ n` is identified
with `B ⧸ 𝔪B ^ n`, by `Ideal.quotEquivOfEq` applied to
`maximalIdealPowQuotientIdeal_eq`. -/
noncomputable def residueFieldMaximalIdealPowQuotientEquivPow (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
    ResidueFieldMaximalIdealPowQuotient A B n ≃+* B ⧸ maximalIdeal B ^ n :=
  Ideal.quotEquivOfEq (maximalIdealPowQuotientIdeal_eq A B n h)

/-- The quotient-ring equivalence fixes quotient representatives, by
`Ideal.quotEquivOfEq_mk`. -/
@[simp]
theorem residueFieldMaximalIdealPowQuotientEquivPow_mk (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n)
    (b : B) :
    residueFieldMaximalIdealPowQuotientEquivPow A B n h
        (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ b :=
  rfl

/-- The `n`-th maximal-ideal graded piece of `B` is `ResidueField A`-linearly
the kernel of the factor map from index `n + 1` to index `n`, when
`map 𝔪A ≤ 𝔪B ^ (n + 1)`. The map sends a graded representative to the
corresponding quotient representative, which lies in the kernel because the
representative lies in `𝔪B ^ n`. Bijectivity goes through the quotient-ring
equivalence `residueFieldMaximalIdealPowQuotientEquivPow` (replacing the source
ideal by `𝔪B ^ (n + 1)`), `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`, and
`Ideal.Quotient.factor_ker`. Residue-base scalar compatibility is checked on
representatives via the scalar tower through `ResidueField B` (there is no
`ResidueField A`-algebra structure on `B`). This is new supporting
infrastructure for the corrected ATLAS N261 quotient-filtration route, not a
source theorem. -/
noncomputable def residueFieldLinearEquivMaximalIdealGradedPieceKerFactor
    (n : ℕ)
    (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      maximalIdeal B ^ (n + 1))
    [IsLocalHom (algebraMap A B)]
    [Module (ResidueField A)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    [IsScalarTower (ResidueField A) (ResidueField B)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)] :
    IsDiscreteValuationRing.MaximalIdealGradedPiece B n ≃ₗ[ResidueField A]
      LinearMap.ker (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap := by
  have hpow : maximalIdeal B ^ (n + 1) ≤ maximalIdeal B ^ n :=
    Ideal.pow_le_pow_right n.le_succ
  have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n :=
    le_trans hSucc hpow
  have hcomm : ∀ b : B,
      residueFieldMaximalIdealPowQuotientEquivPow A B n hmap
          (factorResidueFieldMaximalIdealPowQuotient A B n
            (Ideal.Quotient.mk _ b)) =
        Ideal.Quotient.factor hpow
          (residueFieldMaximalIdealPowQuotientEquivPow A B (n + 1) hSucc
            (Ideal.Quotient.mk _ b)) := by
    intro b
    rw [factorResidueFieldMaximalIdealPowQuotient_mk,
      residueFieldMaximalIdealPowQuotientEquivPow_mk,
      residueFieldMaximalIdealPowQuotientEquivPow_mk, Ideal.Quotient.factor_mk]
  let F : (maximalIdeal B ^ n : Ideal B) →
      LinearMap.ker (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap :=
    fun x =>
      ⟨Ideal.Quotient.mk _ (x : B),
        LinearMap.mem_ker.mpr (by
          simp only [AlgHom.toLinearMap_apply,
            factorResidueFieldMaximalIdealPowQuotient_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_right x.2))⟩
  have F_add : ∀ x y : (maximalIdeal B ^ n : Ideal B),
      F (x + y) = F x + F y := by
    intro x y
    apply Subtype.ext
    change Ideal.Quotient.mk _ (((x + y : _) : B)) =
      Ideal.Quotient.mk _ ((x : B)) + Ideal.Quotient.mk _ ((y : B))
    rw [Submodule.coe_add, map_add]
  have hmem : ∀ a b : (maximalIdeal B ^ n : Ideal B),
      a - b ∈ (maximalIdeal B • ⊤ :
        Submodule B (maximalIdeal B ^ n : Ideal B)) →
      ((a - b : _) : B) ∈ maximalIdeal B ^ (n + 1) := by
    intro a b hab
    simpa [Submodule.mem_smul_top_iff, pow_succ'] using hab
  have F_resp : ∀ a b : (maximalIdeal B ^ n : Ideal B),
      a - b ∈ (maximalIdeal B • ⊤ :
        Submodule B (maximalIdeal B ^ n : Ideal B)) →
      F a = F b := by
    intro a b hab
    have h0 : F (a - b) = 0 := by
      apply Subtype.ext
      change Ideal.Quotient.mk _ (((a - b : _) : B)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Submodule.mem_sup_right (hmem a b hab)
    have hadd : a = b + (a - b) := by abel
    conv_lhs => rw [hadd]
    rw [F_add, h0, add_zero]
  let φ : IsDiscreteValuationRing.MaximalIdealGradedPiece B n →ₗ[ResidueField A]
      LinearMap.ker (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap :=
    { toFun := fun q =>
        Quotient.lift F
          (fun a b h => F_resp a b ((Submodule.quotientRel_def _).mp h)) q
      map_add' := fun x y => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        have hadd : (Submodule.Quotient.mk (x + y) :
              IsDiscreteValuationRing.MaximalIdealGradedPiece B n) =
            (Submodule.Quotient.mk x + Submodule.Quotient.mk y :
              IsDiscreteValuationRing.MaximalIdealGradedPiece B n) := by
          change Submodule.mkQ (maximalIdeal B • ⊤ :
              Submodule B (maximalIdeal B ^ n : Ideal B)) (x + y) =
            Submodule.mkQ (maximalIdeal B • ⊤ :
              Submodule B (maximalIdeal B ^ n : Ideal B)) x +
              Submodule.mkQ (maximalIdeal B • ⊤ :
              Submodule B (maximalIdeal B ^ n : Ideal B)) y
          exact map_add _ _ _
        rw [← hadd]
        exact F_add x y
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨b, hb⟩ := y
        have hsmulG :
            IsLocalRing.residue A a •
              (Submodule.Quotient.mk (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B)) :
                IsDiscreteValuationRing.MaximalIdealGradedPiece B n) =
              Submodule.Quotient.mk
                (⟨algebraMap A B a * b, Ideal.mul_mem_left _ _ hb⟩ :
                  (maximalIdeal B ^ n : Ideal B)) := by
          have htower :
              IsLocalRing.residue A a •
                (Submodule.Quotient.mk (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B)) :
                  IsDiscreteValuationRing.MaximalIdealGradedPiece B n) =
                (algebraMap (ResidueField A) (ResidueField B)
                    (IsLocalRing.residue A a)) •
                  (Submodule.Quotient.mk (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B)) :
                    IsDiscreteValuationRing.MaximalIdealGradedPiece B n) := by
            conv_lhs =>
              rw [← one_smul (ResidueField B)
                (Submodule.Quotient.mk (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B)) :
                  IsDiscreteValuationRing.MaximalIdealGradedPiece B n),
                ← smul_assoc]
            congr 1
            rw [Algebra.smul_def, mul_one]
          rw [htower, IsLocalRing.ResidueField.algebraMap_residue]
          exact Module.Quotient.mk_smul_mk _ _ _ _
        rw [hsmulG]
        change F _ = IsLocalRing.residue A a •
          F (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B))
        apply Subtype.ext
        change Ideal.Quotient.mk _ (algebraMap A B a * b) =
          ((IsLocalRing.residue A a •
            F (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B))) :
            LinearMap.ker _).val
        rw [show ((IsLocalRing.residue A a •
              F (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B))) :
              LinearMap.ker _).val =
            IsLocalRing.residue A a •
              Ideal.Quotient.mk
                (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔
                  maximalIdeal B ^ (n + 1))
                b from rfl,
          Algebra.smul_def,
          show algebraMap (ResidueField A)
              (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
              (IsLocalRing.residue A a) =
            Ideal.Quotient.mk _ (algebraMap A B a) from rfl, map_mul] }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    ext q
    simp only [Submodule.mem_bot, LinearMap.mem_ker]
    constructor
    · intro hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨b, hb⟩ := x
      have hF : F (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B)) = 0 := hq
      have hval : Ideal.Quotient.mk
          (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ (n + 1))
          b = 0 := congrArg Subtype.val hF
      have hB : Ideal.Quotient.mk (maximalIdeal B ^ (n + 1)) b = 0 := by
        have hcongr := congrArg
          (residueFieldMaximalIdealPowQuotientEquivPow A B (n + 1) hSucc) hval
        simpa [residueFieldMaximalIdealPowQuotientEquivPow_mk] using hcongr
      have hrep : Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow (maximalIdeal B) n
            (Submodule.Quotient.mk (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B))) =
            (⟨Ideal.Quotient.mk (maximalIdeal B ^ (n + 1)) b,
              Ideal.mem_map_of_mem _ hb⟩ :
              Ideal.map (Ideal.Quotient.mk (maximalIdeal B ^ (n + 1)))
                (maximalIdeal B ^ n)) := rfl
      have e0 : Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow (maximalIdeal B) n
            (Submodule.Quotient.mk (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B))) = 0 := by
        rw [hrep]
        simp [hB]
      have hzero : (Submodule.Quotient.mk (⟨b, hb⟩ : (maximalIdeal B ^ n : Ideal B)) :
          IsDiscreteValuationRing.MaximalIdealGradedPiece B n) = 0 := by
        have hinjE :=
          (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow (maximalIdeal B) n).injective
        apply hinjE
        rw [e0, map_zero]
      exact hzero
    · intro hq
      rw [hq, map_zero]
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hfactor0 : factorResidueFieldMaximalIdealPowQuotient A B n
        (Ideal.Quotient.mk _ b) = 0 :=
      LinearMap.mem_ker.mp hy
    have hkerB : Ideal.Quotient.factor hpow
        (residueFieldMaximalIdealPowQuotientEquivPow A B (n + 1) hSucc
          (Ideal.Quotient.mk _ b)) = 0 := by
      rw [← hcomm b, hfactor0, map_zero]
    have hmemMap :
        residueFieldMaximalIdealPowQuotientEquivPow A B (n + 1) hSucc
            (Ideal.Quotient.mk _ b) ∈
          Ideal.map (Ideal.Quotient.mk (maximalIdeal B ^ (n + 1)))
            (maximalIdeal B ^ n) := by
      rw [← Ideal.Quotient.factor_ker hpow]
      exact RingHom.mem_ker.mpr hkerB
    obtain ⟨b', hb', hbe⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
      hmemMap
    rw [residueFieldMaximalIdealPowQuotientEquivPow_mk] at hbe
    have hsub : Ideal.Quotient.mk (maximalIdeal B ^ (n + 1)) (b' - b) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hbe
    have hmem' : b' - b ∈ maximalIdeal B ^ (n + 1) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hsub
    refine ⟨Submodule.Quotient.mk (⟨b', hb'⟩ : (maximalIdeal B ^ n : Ideal B)), ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk
      (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ (n + 1)) b' =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ (n + 1)) b
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Submodule.mem_sup_right hmem'
  exact LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
