/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean -/

import sympy.atlas.GroupTheory.BurnsidePaqbReduction
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

/-!
Character-orthogonality stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ColumnOrth.lean`.
-/

open CategoryTheory

namespace BurnsidePaqb

variable (G : Type) [Group G] [Fintype G]

omit [Fintype G] in
/-- The group order is nonzero in `ℂ`. -/
instance [Finite G] : NeZero (Nat.card G : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)⟩

/-- The group order is invertible in `ℂ`. -/
noncomputable instance : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (NeZero.ne _)

omit [Fintype G] in
/-- Bridge (forward): an irreducible complex representation gives a simple `FDRep`. -/
theorem simple_fdrep_of_irreducible {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Finite G] (σ : Representation ℂ G V) [σ.IsIrreducible] :
    Simple (FDRep.of σ) := by
  rw [FDRep.simple_iff_end_is_rank_one]
  have e1 := Representation.linHom.invariantsEquivFDRepHom (FDRep.of σ) (FDRep.of σ)
  have e2 := Representation.invariantsEquivIntertwiningMap (FDRep.of σ).ρ (FDRep.of σ).ρ
  rw [← LinearEquiv.finrank_eq e1, LinearEquiv.finrank_eq e2]
  change Module.finrank ℂ (σ.IntertwiningMap σ) = 1
  exact Representation.IsIrreducible.finrank_intertwiningMap_self σ

/-- Isomorphism classes of simple `FDRep`s: two simples are related when isomorphic. -/
def Simple.isoSetoid : Setoid {V : FDRep ℂ G // Simple V} where
  r S T := Nonempty (S.1 ≅ T.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun h => h.elim fun i => ⟨i.symm⟩,
    fun h1 h2 => h1.elim fun i => h2.elim fun j => ⟨i.trans j⟩⟩

/-- Iso-classes of simple finite-dimensional complex representations. -/
def Irr : Type 1 := Quotient (Simple.isoSetoid G)

/-- Character of a class, well-defined by `FDRep.char_iso`. -/
noncomputable def Irr.charFun (c : Irr G) : G → ℂ :=
  Quotient.lift (fun S => S.1.character) (fun S T h => by
    obtain ⟨i⟩ := h
    exact FDRep.char_iso i) c

omit [Fintype G] in
theorem Irr.charFun_mk (S : {V : FDRep ℂ G // Simple V}) :
    Irr.charFun G (Quotient.mk _ S) = S.1.character := rfl

/-- Chosen representative bundle of a class. -/
noncomputable def Irr.repBundle (c : Irr G) : {V : FDRep ℂ G // Simple V} :=
  Quotient.out c

omit [Fintype G] in
theorem Irr.mk_repBundle (c : Irr G) : Quotient.mk _ (Irr.repBundle G c) = c :=
  Quotient.out_eq c

omit [Fintype G] in
theorem Irr.charFun_repBundle (c : Irr G) :
    (Irr.repBundle G c).1.character = Irr.charFun G c := by
  have h := Irr.charFun_mk G (Irr.repBundle G c)
  rw [Irr.mk_repBundle] at h
  exact h.symm

/-- The trivial representation is irreducible: submodules of `ℂ` are `⊥`/`⊤`. -/
instance trivial_isIrreducible : (Representation.trivial ℂ G ℂ).IsIrreducible :=
  @IsSimpleOrder.of_forall_eq_top _ _ _
    ⟨⊤, ⊥, fun h => by
      have htop : (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule
          = ⊤ := rfl
      have hbot : (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule
          = ⊥ := rfl
      have hsub : (⊤ : Submodule ℂ ℂ) = ⊥ := by rw [← htop, ← hbot, h]
      have h1 : (1 : ℂ) ∈ (⊤ : Submodule ℂ ℂ) := Submodule.mem_top
      rw [hsub] at h1
      simp at h1⟩
    fun U hU => by
      rcases eq_bot_or_eq_top U.toSubmodule with h | h
      · exfalso
        apply hU
        have hU' : U.toSubmodule
            = (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule := by
          rw [h]; rfl
        exact Subrepresentation.toSubmodule_injective hU'
      · have hU' : U.toSubmodule
            = (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule := by
          rw [h]; rfl
        exact Subrepresentation.toSubmodule_injective hU'

/-- The iso-class of the trivial representation. -/
noncomputable def Irr.triv : Irr G :=
  Quotient.mk _
    ⟨FDRep.of (Representation.trivial ℂ G ℂ),
      simple_fdrep_of_irreducible G (Representation.trivial ℂ G ℂ)⟩

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

/-- Class functions: constant on conjugacy classes. -/
def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

/-- Every finite set of iso-classes has cardinality at most `|G|`. -/
theorem cardBound (s : Finset (Irr G)) : s.card ≤ Fintype.card G := by
  classical
  have hli : LinearIndependent ℂ (fun i : ↥s => Irr.charFun G (i : Irr G)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hfun : ∀ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) = 0 := by
      intro x
      have hcon := congrFun hg x
      simpa using hcon
    intro j
    have hexpand : (Nat.card G : ℂ)⁻¹ *
        ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹ = g j := by
      have step1 : ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹
          = ∑ i, g i * (∑ x : G, Irr.charFun G ((i : ↥s) : Irr G) x *
            Irr.charFun G ((j : ↥s) : Irr G) x⁻¹) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        simp [smul_eq_mul, mul_assoc]
      rw [step1, Finset.mul_sum]
      trans ∑ i : ↥s, (if ((i : ↥s) : Irr G) = (j : ↥s) then g i else 0)
      · refine Finset.sum_congr rfl fun i _ => ?_
        have hi := charInner_orth G ((i : ↥s) : Irr G) ((j : ↥s) : Irr G)
        rw [mul_left_comm, hi]
        by_cases hij : ((i : ↥s) : Irr G) = (j : ↥s)
        · rw [ite_eq_left hij, ite_eq_left hij, mul_one]
        · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]
      · simp_rw [Subtype.ext_iff.symm]
        exact Fintype.sum_ite_eq' j g
    have h2 : (Nat.card G : ℂ)⁻¹ *
        ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹ = 0 := by
      simp_rw [hfun, zero_mul, Finset.sum_const_zero, mul_zero]
    rw [hexpand] at h2
    exact h2
  have h := LinearIndependent.fintype_card_le_finrank hli
  rw [Module.finrank_pi] at h
  rwa [Fintype.card_coe] at h

omit [Fintype G] in
/-- Iso-classes form a finite type. -/
noncomputable instance [Finite G] : Finite (Irr G) := by
  let _ : Fintype G := Fintype.ofFinite G
  rw [← not_infinite_iff_finite]
  intro hInf
  have e := Infinite.natEmbedding (Irr G)
  set N := Fintype.card G
  have hcard := cardBound G (Finset.map e (Finset.range (N + 1)))
  rw [Finset.card_map, Finset.card_range] at hcard
  omega

noncomputable instance : Fintype (Irr G) := Fintype.ofFinite _

/-- Zimmerman's averaging operator for a function `f`. -/
noncomputable def zimmOp (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (f : G → ℂ) :
    Module.End ℂ M :=
  ∑ g : G, f g • (Representation.ofModule' (k := ℂ) M) g⁻¹

-- Carrier of the regular module.
abbrev RegMod : Type := ↥(⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))

open Classical in
/-- The delta class function at the identity. -/
noncomputable def deltaOne : G → ℂ := fun g => if g = 1 then 1 else 0
end BurnsidePaqb
