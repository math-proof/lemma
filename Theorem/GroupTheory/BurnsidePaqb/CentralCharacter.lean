/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean -/

import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorem.GroupTheory.BurnsidePaqb.ClassSum.Part3
import Lemma.Nat.ConjClass.of.IsConj
/-!
Central-character stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/CentralChar.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- A central group-algebra element acts on an irreducible representation by a
scalar (Schur's lemma via `asAlgebraHom`). -/
theorem exists_scalar_of_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ]
    (z : MonoidAlgebra ℂ G) (hz : ∀ w, w * z = z * w) :
    ∃ c : ℂ, ∀ v : V, ρ.asAlgebraHom z v = c • v := by
  classical
  let L : Module.End (MonoidAlgebra ℂ G) ρ.asModule :=
    { toFun := fun v => z • v
      map_add' := fun x y => smul_add z x y
      map_smul' := fun r x => by
        change z • (r • x) = r • (z • x)
        rw [← smul_assoc, ← smul_assoc]
        change (z * r) • x = (r * z) • x
        rw [(hz r).symm] }
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ).2 L
  refine ⟨c, fun v => ?_⟩
  have h1 : (algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) c)
      (ρ.asModuleEquiv.symm v) = L (ρ.asModuleEquiv.symm v) := by rw [hc]
  have h2 : ∀ x : ρ.asModule,
      (algebraMap ℂ (Module.End (MonoidAlgebra ℂ G) ρ.asModule) c) x = c • x := by
    intro x
    simp [Algebra.algebraMap_eq_smul_one]
  have hL : ∀ x : ρ.asModule, L x = z • x := fun x => rfl
  rw [h2, hL] at h1
  have h4 : ρ.asModuleEquiv (c • ρ.asModuleEquiv.symm v) =
      ρ.asModuleEquiv (z • ρ.asModuleEquiv.symm v) := congrArg _ h1
  rw [map_smul, LinearEquiv.apply_symm_apply, ρ.asModuleEquiv_map_smul,
    LinearEquiv.apply_symm_apply] at h4
  exact h4.symm

end BurnsidePaqb
