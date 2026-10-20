/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.Basic.Complex.Basic

import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Analysis.Complex.Polynomial.Basic

open CategoryTheory
open scoped IsMulCommutative

namespace MathlibExt.GroupTheory.AbelianRepresentationWanted

/-!
# Representations of finite abelian groups

That irreducible representations of a commutative group are one-dimensional
is `Representation.Irreducible.finrank_eq_one_of_isMulCommutative`; the
classification itself is recorded here: every simple complex representation
of a finite abelian group has a monoid-homomorphism character, every such
homomorphism occurs, and the character determines the representation up to
isomorphism.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "representations of abelian groups" (reference-only, no Lean
formalization); J.-P. Serre, Linear Representations of Finite Groups, GTM 42,
§2.8 and Ch. I (representations of abelian groups); K. Conrad, Character
theory notes, https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf.
-/

/-- A categorically simple finite-dimensional representation has an irreducible underlying
representation. -/
theorem _root_.FDRep.isIrreducible_of_simple {k G : Type*} [Field k] [Monoid G]
    (V : FDRep k G) [Simple V] : Representation.IsIrreducible V.ρ := by
  let _ : Nontrivial V := by
    by_contra h
    let _ : Subsingleton V := not_nontrivial_iff_subsingleton.mp h
    apply CategoryTheory.id_nonzero V
    ext x
    exact Subsingleton.elim _ _
  change IsSimpleOrder (Subrepresentation V.ρ)
  rw [isSimpleOrder_iff]
  constructor
  · refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'
  · intro S
    let U : FDRep k G := FDRep.of S.toRepresentation
    let jRep :
        (forget₂ (FDRep k G) (Rep k G)).obj U ⟶
          (forget₂ (FDRep k G) (Rep k G)).obj V :=
      Rep.ofHom ⟨S.toSubmodule.subtype, by intro g; ext x; rfl⟩
    let j : U ⟶ V := (FDRep.forget₂HomLinearEquiv U V) jRep
    have hj_map : (forget₂ (FDRep k G) (Rep k G)).map j = jRep := by
      change (FDRep.forget₂HomLinearEquiv U V).symm
          ((FDRep.forget₂HomLinearEquiv U V) jRep) = jRep
      exact LinearEquiv.symm_apply_apply _ _
    have hjRep_mono : Mono jRep := (Rep.mono_iff_injective jRep).2 Subtype.val_injective
    let _ : Mono jRep := hjRep_mono
    have hj_mono : Mono j :=
      (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map <| hj_map ▸ hjRep_mono
    let _ : Mono j := hj_mono
    by_cases hj_zero : j = 0
    · left
      apply Subrepresentation.toSubmodule_injective
      apply (Submodule.eq_bot_iff _).mpr
      intro x hx
      let y : S.toSubmodule := ⟨x, hx⟩
      have hjRep_zero : jRep = 0 := by
        rw [← hj_map, hj_zero]
        simp
      have hy := ConcreteCategory.congr_hom hjRep_zero y
      change (x : V) = 0 at hy
      exact hy
    · right
      let _ : IsIso j := (Simple.mono_isIso_iff_nonzero j).2 hj_zero
      let _ : IsIso jRep := hj_map ▸ inferInstanceAs (IsIso ((forget₂ _ _).map j))
      have hjRep_surjective : Function.Surjective jRep :=
        (ConcreteCategory.isIso_iff_bijective jRep).mp inferInstance |>.2
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.eq_top_iff'.mpr
      intro x
      obtain ⟨y, hy⟩ := hjRep_surjective x
      change S.toSubmodule at y
      change (y : V) = x at hy
      rw [← hy]
      exact y.property

/-- A simple representation of a multiplicatively commutative monoid over an algebraically closed
field is one-dimensional. -/
theorem _root_.FDRep.finrank_eq_one_of_isMulCommutative
    {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
    (V : FDRep k G) [Simple V] : Module.finrank k V = 1 := by
  let _ : Representation.IsIrreducible V.ρ := V.isIrreducible_of_simple
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative V.ρ

/-- On a simple representation of a multiplicatively commutative monoid, every group action is
scalar multiplication by its character value. -/
theorem _root_.FDRep.rho_eq_character_smul_of_simple
    {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
    (V : FDRep k G) [Simple V] (g : G) :
    V.ρ g = V.character g • LinearMap.id := by
  have hdim := V.finrank_eq_one_of_isMulCommutative
  obtain ⟨c, hc, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (V.ρ g)
  have htrace := congrArg (LinearMap.trace k V) hc
  have hcharacter : V.character g = c := by
    simpa [FDRep.character, hdim] using htrace
  rw [hcharacter]
  exact hc

/-- The character of a simple representation of a multiplicatively commutative monoid is
multiplicative. -/
theorem _root_.FDRep.character_mul_of_simple
    {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
    (V : FDRep k G) [Simple V] (g h : G) :
    V.character (g * h) = V.character g * V.character h := by
  have hdim := V.finrank_eq_one_of_isMulCommutative
  have hmaps :
      V.character (g * h) • (LinearMap.id : V →ₗ[k] V) =
        (V.character g * V.character h) • LinearMap.id := by
    rw [← V.rho_eq_character_smul_of_simple, V.ρ.map_mul,
      V.rho_eq_character_smul_of_simple, V.rho_eq_character_smul_of_simple]
    ext x
    simp [smul_smul, mul_comm]
  have htrace := congrArg (LinearMap.trace k V) hmaps
  simpa [hdim] using htrace

/-- The character of a simple representation of a multiplicatively commutative monoid, bundled as
a monoid homomorphism. -/
noncomputable def _root_.FDRep.characterMonoidHom
    {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
    (V : FDRep k G) [Simple V] : G →* k where
  toFun := V.character
  map_one' := by simp [V.finrank_eq_one_of_isMulCommutative]
  map_mul' := V.character_mul_of_simple

/-- The monoid homomorphism underlying `FDRep.characterMonoidHom` is the character. -/
@[simp]
theorem _root_.FDRep.coe_characterMonoidHom
    {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
    (V : FDRep k G) [Simple V] : ⇑V.characterMonoidHom = V.character := rfl

/-- The one-dimensional finite-dimensional representation associated to a monoid homomorphism into
a field. -/
noncomputable def _root_.FDRep.ofMonoidHom {k G : Type*} [Field k] [Monoid G]
    (φ : G →* k) : FDRep k G :=
  FDRep.of
    { toFun := fun g => φ g • (LinearMap.id : k →ₗ[k] k)
      map_one' := by
        ext
        simp
      map_mul' := by
        intro g h
        ext
        simp [mul_smul, mul_comm] }

/-- In `FDRep.ofMonoidHom φ`, the element `g` acts by the scalar `φ g`. -/
@[simp]
theorem _root_.FDRep.ofMonoidHom_ρ {k G : Type*} [Field k] [Monoid G]
    (φ : G →* k) (g : G) : (FDRep.ofMonoidHom φ).ρ g = φ g • LinearMap.id := by
  change (φ g • (LinearMap.id : k →ₗ[k] k)) = _
  rfl

/-- The representation `FDRep.ofMonoidHom φ` is one-dimensional. -/
@[simp]
theorem _root_.FDRep.ofMonoidHom_finrank {k G : Type*} [Field k] [Monoid G]
    (φ : G →* k) : Module.finrank k (FDRep.ofMonoidHom φ) = 1 := by
  change Module.finrank k k = 1
  simp

/-- The character of `FDRep.ofMonoidHom φ` is `φ`. -/
@[simp]
theorem _root_.FDRep.ofMonoidHom_character {k G : Type*} [Field k] [Monoid G]
    (φ : G →* k) : (FDRep.ofMonoidHom φ).character = φ := by
  ext g
  change LinearMap.trace k k (φ g • LinearMap.id) = φ g
  simp

/-- The one-dimensional representation `FDRep.ofMonoidHom φ` is simple. -/
theorem _root_.FDRep.ofMonoidHom_simple {k G : Type*} [Field k] [Monoid G]
    (φ : G →* k) : Simple (FDRep.ofMonoidHom φ) := by
  let _ : Simple ((forget₂ (FGModuleCat k) (ModuleCat k)).obj (FGModuleCat.of k k)) := by
    change Simple (ModuleCat.of k k)
    exact simple_of_finrank_eq_one (k := k) (R := k) (by simp)
  let hfg : Simple (FGModuleCat.of k k) :=
    Functor.simple_of_simple_obj (forget₂ (FGModuleCat k) (ModuleCat k)) _
  let _ : Simple (FGModuleCat.of k k) := hfg
  let _ : (Action.forget (FGModuleCat k) G).ReflectsIsomorphisms :=
    ⟨fun f hf => by
      let _ : IsIso f.hom := hf
      infer_instance⟩
  unfold FDRep.ofMonoidHom
  let _ : Simple
      ((Action.forget (FGModuleCat k) G).obj
        (FDRep.of
          { toFun := fun g => φ g • (LinearMap.id : k →ₗ[k] k)
            map_one' := by ext; simp
            map_mul' := by intro g h; ext; simp [mul_smul, mul_comm] })) := by
    change Simple (FGModuleCat.of k k)
    exact hfg
  exact Functor.simple_of_simple_obj (Action.forget (FGModuleCat k) G) _

/--
The character of a simple complex representation of a finite abelian group is
a monoid homomorphism.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "representations of abelian groups"; J.-P. Serre, Linear
Representations of Finite Groups, GTM 42, §2.8 (degree-one characters of
abelian groups).

Proves `Wanted` entry `abelian_simple_char_is_hom`.

Proof: Categorical simplicity gives irreducibility, then Mathlib's commutative irreducible
representation theorem makes `V` one-dimensional (the corollary in Wikipedia, “Schur's lemma”,
that complex irreducible representations of abelian groups are one-dimensional). Rank-one
endomorphisms are scalars, and their traces give the multiplicative character.
-/
theorem abelian_simple_char_is_hom (G : Type*) [CommGroup G]
    [Finite G] (V : FDRep ℂ G) [Simple V] :
    ∃ φ : G →* ℂ, V.character = ⇑φ := by
  exact ⟨V.characterMonoidHom, V.coe_characterMonoidHom.symm⟩

/--
Every monoid homomorphism to `ℂ` is the character of a simple complex
representation of a finite abelian group.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "representations of abelian groups"; J.-P. Serre, Linear
Representations of Finite Groups, GTM 42, Ch. I (one-dimensional
representations from characters).

Proves `Wanted` entry `abelian_hom_is_simple_char`.

Proof: Let `g` act on the one-dimensional space `ℂ` by the scalar `φ g`; its trace is `φ g`.
One-dimensional modules are simple. Wikipedia, “Representation theory of finite groups”, notes that
the irreducible characters of an abelian group are its homomorphisms to `ℂˣ`.
-/
theorem abelian_hom_is_simple_char (G : Type*) [CommGroup G]
    [Finite G] (φ : G →* ℂ) :
    ∃ V : FDRep ℂ G, Simple V ∧ V.character = ⇑φ := by
  exact ⟨FDRep.ofMonoidHom φ, FDRep.ofMonoidHom_simple φ, FDRep.ofMonoidHom_character φ⟩

private theorem abelianRep_simple_iso_of_char_eq (G : Type*) [CommGroup G] [Finite G]
    (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  classical
  let _ := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : ℂ) := invertibleOfNonzero <| by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  have hVV := FDRep.char_orthonormal V V
  have hVW := FDRep.char_orthonormal V W
  rw [← h] at hVW
  rw [ite_eq_left ⟨Iso.refl V⟩] at hVV
  have hif : (if Nonempty (V ≅ W) then (1 : ℂ) else 0) = 1 := by
    rw [← hVW]
    exact hVV
  by_cases hVW_nonempty : Nonempty (V ≅ W)
  · exact hVW_nonempty
  · simp [hVW_nonempty] at hif

/--
Simple complex representations of a finite abelian group with equal characters
are isomorphic.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "representations of abelian groups"; J.-P. Serre, Linear
Representations of Finite Groups, GTM 42, §2.8 (characters determine
representations of abelian groups).

Proves `Wanted` entry `abelian_simple_iso_of_char_eq`.

Proof: Mathlib's character orthonormality formula gives inner product one for `V` with itself.
Replacing the second character by the equal character of `W` forces `V ≅ W`. This is the
orthonormality of irreducible characters in Wikipedia, “Character theory”.
-/
theorem abelian_simple_iso_of_char_eq (G : Type*) [CommGroup G]
    [Finite G] (V W : FDRep ℂ G) [Simple V] [Simple W]
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  exact abelianRep_simple_iso_of_char_eq G V W h

end MathlibExt.GroupTheory.AbelianRepresentationWanted
