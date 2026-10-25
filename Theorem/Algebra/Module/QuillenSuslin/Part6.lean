/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Ring
import Def.Algebra.Module.QuillenSuslin.Part6
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qsResidueMonicMap_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (p : Polynomial R) :
    qsResidueMonicMap R
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) =
      algebraMap (Polynomial (IsLocalRing.ResidueField R))
        (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))
        (p.map (IsLocalRing.residue R)) := by
  let f := Polynomial.mapRingHom (IsLocalRing.residue R)
  have hsub : (qsMonicSubmonoid R).map f =
      qsMonicSubmonoid (IsLocalRing.ResidueField R) :=
    qs_map_monicSubmonoid_eq _ IsLocalRing.residue_surjective
  let _ : IsLocalization ((qsMonicSubmonoid R).map f)
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) := by
    rw [hsub]
    infer_instance
  change (IsLocalization.map
    (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) f
      (qsMonicSubmonoid R).le_comap_map)
        (algebraMap (Polynomial R) (Localization (qsMonicSubmonoid R)) p) = _
  exact IsLocalization.map_eq _ _

theorem qsResidueMonicMap_mk
    (R : Type*) [CommRing R] [IsLocalRing R]
    (p : Polynomial R) (s : qsMonicSubmonoid R) :
    qsResidueMonicMap R (Localization.mk p s) =
      Localization.mk (p.map (IsLocalRing.residue R))
        (⟨(s : Polynomial R).map (IsLocalRing.residue R),
          s.property.map (IsLocalRing.residue R)⟩ :
          qsMonicSubmonoid (IsLocalRing.ResidueField R)) := by
  let f := Polynomial.mapRingHom (IsLocalRing.residue R)
  have hsub : (qsMonicSubmonoid R).map f =
      qsMonicSubmonoid (IsLocalRing.ResidueField R) :=
    qs_map_monicSubmonoid_eq _ IsLocalRing.residue_surjective
  let _ : IsLocalization ((qsMonicSubmonoid R).map f)
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) := by
    rw [hsub]
    infer_instance
  change (IsLocalization.map
    (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) f
      (qsMonicSubmonoid R).le_comap_map) (Localization.mk p s) = _
  rw [Localization.mk_eq_mk', IsLocalization.map_mk', Localization.mk_eq_mk']
  rfl

theorem qsPolynomialPart_map_residue
    (R : Type*) [CommRing R] [IsLocalRing R]
    (z : Localization (qsMonicSubmonoid R)) :
    (qsPolynomialPart R z).map (IsLocalRing.residue R) =
      qsPolynomialPart (IsLocalRing.ResidueField R) (qsResidueMonicMap R z) := by
  induction z using Localization.induction_on with
  | _ x =>
    obtain ⟨p, s⟩ := x
    rw [qsResidueMonicMap_mk]
    change (p /ₘ (s : Polynomial R)).map (IsLocalRing.residue R) =
      p.map (IsLocalRing.residue R) /ₘ
        (s : Polynomial R).map (IsLocalRing.residue R)
    exact Polynomial.map_divByMonic (IsLocalRing.residue R) s.property

end QuillenSuslin
