/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.QCohProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohEquivalenceProof
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof

set_option maxHeartbeats 4000000

open MvPolynomial QCohProjective

noncomputable section

namespace TwistSheaf

variable (k : Type*) [Field k] (n : ℕ)


/-- The `k`-module structure on the multivariate polynomial ring `k[X₀,…,Xₙ]`. -/
noncomputable instance mvPolyModule :
    Module k (MvPolynomial (Fin (n + 1)) k) := Algebra.toModule

/-- The `k`-submodule of polynomials of homogeneous degree `d`, defined for
all integers `d` by setting it to `⊥` for `d < 0`. -/
def polyGrSub (d : ℤ) : Submodule k (HomogCoordRing k n) :=
  if 0 ≤ d then homogeneousSubmodule (Fin (n + 1)) k d.toNat else ⊥

/-- The degree-`d` graded component as a type. -/
abbrev polyGrComp (d : ℤ) : Type _ := ↥(polyGrSub k n d)

/-- Graded multiplication: multiplying a degree-`i` homogeneous polynomial
with a degree-`j` graded element gives a degree-`(i+j)` graded element. -/
def polyGsmul (i : ℕ) (j : ℤ) :
    gradedComponent k n i → polyGrComp k n j → polyGrComp k n (↑i + j) :=
  fun ⟨s, hs⟩ ⟨m, hm⟩ => by
    refine ⟨s * m, ?_⟩
    by_cases hj : 0 ≤ j
    ·
      simp only [polyGrSub, if_pos hj] at hm
      simp only [polyGrSub, if_pos (by omega : (0 : ℤ) ≤ ↑i + j)]
      show (s * m).IsHomogeneous (↑i + j).toNat
      have hs' : s.IsHomogeneous i := hs
      have hm' : m.IsHomogeneous j.toNat := hm
      convert hs'.mul hm' using 1
      omega
    ·
      push Not at hj
      simp only [polyGrSub, if_neg (by omega : ¬(0 ≤ j))] at hm
      replace hm : m = 0 := by simpa using hm
      rw [hm, mul_zero]
      exact Submodule.zero_mem _

/-- Graded-module data realizing the structure sheaf of `P^n` as the trivial
shift: the graded pieces are the homogeneous components of `k[X₀,…,Xₙ]`. -/
def structureSheafData : GradedModuleData k n where
  component := polyGrComp k n
  instACG := fun _ => inferInstance
  instMod := fun _ => inferInstance
  gsmul := polyGsmul k n

/-- The Serre twist `O(d)` on `P^n`, expressed as the graded-module data
obtained by shifting the structure sheaf by `d`. -/
def serreTwist (d : ℤ) : GradedModuleData k n :=
  (structureSheafData k n).twist d
