import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory


/--
[proposition_23_57](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2357.lean)
-/
@[path]
lemma proposition_23_57
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {M N : C}
  {f : M ⟶ N}
  {P : ProjectiveResolution M}
  {Q : ProjectiveResolution N} :
-- imply
  (∃ α : P.complex ⟶ Q.complex, α ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) ∧ (∀ (g h : P.complex ⟶ Q.complex), g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f → h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f → Nonempty (Homotopy g h)) :=
-- proof
  ⟨⟨ProjectiveResolution.lift f P Q, ProjectiveResolution.lift_commutes f P Q⟩,
    fun g h hg hh => ⟨ProjectiveResolution.liftHomotopy f g h hg hh⟩⟩

/--
[proposition_23_57_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2357.lean)
-/
@[path]
lemma proposition_23_57_injective
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {M N : C}
  {f : M ⟶ N}
  {I : InjectiveResolution M}
  {J : InjectiveResolution N} :
-- imply
  (∃ α : I.cocomplex ⟶ J.cocomplex, I.ι ≫ α = (CochainComplex.single₀ C).map f ≫ J.ι) ∧ (∀ (g h : I.cocomplex ⟶ J.cocomplex), I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι → I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι → Nonempty (Homotopy g h)) :=
-- proof
  ⟨⟨InjectiveResolution.desc f J I, InjectiveResolution.desc_commutes f J I⟩,
    fun g h hg hh => ⟨InjectiveResolution.descHomotopy f g h hg hh⟩⟩

/--
[resolution_comparison_unique_up_to_homotopy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2357.lean)
-/
@[path]
lemma resolution_comparison_unique_up_to_homotopy
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {M N : C}
  {f : M ⟶ N}
  {P : ProjectiveResolution M}
  {Q : ProjectiveResolution N}
  {I : InjectiveResolution M}
  {J : InjectiveResolution N} :
-- imply
  ((∃ α : P.complex ⟶ Q.complex, α ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) ∧ (∀ (g h : P.complex ⟶ Q.complex), g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f → h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f → Nonempty (Homotopy g h))) ∧ ((∃ α : I.cocomplex ⟶ J.cocomplex, I.ι ≫ α = (CochainComplex.single₀ C).map f ≫ J.ι) ∧ (∀ (g h : I.cocomplex ⟶ J.cocomplex), I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι → I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι → Nonempty (Homotopy g h))) :=
-- proof
  ⟨proposition_23_57 f P Q, proposition_23_57_injective f I J⟩


-- created on 2026-10-23
