import Mathlib
import sympy.Basic
import Lemma.ModularCurve.EtaQuotient
import Lemma.Int.P2MUtil

open Complex ModularGroup
open UpperHalfPlane hiding I
open scoped ModularForm MatrixGroups Real Topology
open ModularCurve

/--
[ModularCurve_sharpUnitNecessary_of_eisensteinNumerator_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_sharpUnitNecessary_of_eisensteinNumerator_eq_one.lean)
-/

private lemma  sharpUnitNecessary_of_eisensteinNumerator_eq_one
  (ℓ : ℕ)
  (h : eisensteinNumerator ℓ = 1) :
  SharpUnitNecessary ℓ :=
  fun m _ _ _ _ _ => h ▸ one_dvd m
@[path]
private lemma main
  {ℓ : ℕ}
-- given
  (h : ModularCurve.eisensteinNumerator ℓ = 1) :
-- imply
  ModularCurve.SharpUnitNecessary ℓ :=
-- proof
  sharpUnitNecessary_of_eisensteinNumerator_eq_one ℓ h


-- created on 2026-10-23
