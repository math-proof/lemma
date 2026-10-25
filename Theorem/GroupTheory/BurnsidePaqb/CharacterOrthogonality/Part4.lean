/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean -/

import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Def.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part3
open CategoryTheory

/-!
Character-orthogonality stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ColumnOrth.lean`.
-/


namespace BurnsidePaqb

variable (G : Type) [Group G] [Fintype G]

open Classical in
/-- Row orthogonality over iso-classes. -/
theorem charInner_orth (i j : Irr G) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, Irr.charFun G i g * Irr.charFun G j g⁻¹ =
      if i = j then 1 else 0 := by
  classical
  have := (Irr.repBundle G i).2
  have := (Irr.repBundle G j).2
  have hi := Irr.charFun_repBundle G i
  have hj := Irr.charFun_repBundle G j
  rw [← hi, ← hj]
  have h := FDRep.char_orthonormal (k := ℂ) (Irr.repBundle G i).1 (Irr.repBundle G j).1
  rw [h]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left ⟨Iso.refl _⟩]
  · rw [ite_eq_right hij, ite_eq_right]
    intro hcon
    apply hij
    obtain ⟨e⟩ := hcon
    have hq : Quotient.mk (Simple.isoSetoid G) (Irr.repBundle G i) =
        Quotient.mk (Simple.isoSetoid G) (Irr.repBundle G j) :=
      Quotient.eq.mpr ⟨e⟩
    rw [Irr.mk_repBundle, Irr.mk_repBundle] at hq
    exact hq

end BurnsidePaqb
