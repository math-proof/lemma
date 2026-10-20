import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.AbelianRepresentation
open CategoryTheory
open scoped IsMulCommutative
open MathlibExt.GroupTheory.AbelianRepresentationWanted


/--
[_root_.FDRep.isIrreducible_of_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_isIrreducible_of_simple_eq
  [Field k] [Monoid G]
  {V : FDRep k G} [Simple V] :
-- imply
  Representation.IsIrreducible V.ρ := by
-- proof
  apply FDRep.isIrreducible_of_simple V

/--
[_root_.FDRep.finrank_eq_one_of_isMulCommutative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_finrank_eq_one_of_isMulCommutative_eq
  [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
  {V : FDRep k G} [Simple V] :
-- imply
  Module.finrank k V = 1 := by
-- proof
  apply FDRep.finrank_eq_one_of_isMulCommutative V

/--
[_root_.FDRep.rho_eq_character_smul_of_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_rho_eq_character_smul_of_simple_eq
  [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
  {V : FDRep k G} [Simple V]
  {g : G} :
-- imply
  V.ρ g = V.character g • LinearMap.id := by
-- proof
  apply FDRep.rho_eq_character_smul_of_simple V g

/--
[_root_.FDRep.character_mul_of_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_character_mul_of_simple_eq
  [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
  {V : FDRep k G} [Simple V]
  {g h : G} :
-- imply
  V.character (g * h) = V.character g * V.character h := by
-- proof
  apply FDRep.character_mul_of_simple V g h

/--
[_root_.FDRep.coe_characterMonoidHom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_coe_characterMonoidHom_eq
  [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
  {V : FDRep k G} [Simple V] :
-- imply
  ⇑V.characterMonoidHom = V.character := by
-- proof
  apply FDRep.coe_characterMonoidHom V

/--
[_root_.FDRep.ofMonoidHom_](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_ofMonoidHom__eq
  [Field k] [Monoid G]
  {φ : G →* k}
  {g : G} :
-- imply
  (FDRep.ofMonoidHom φ).ρ g = φ g • LinearMap.id := by
-- proof
  apply FDRep.ofMonoidHom_ φ g

/--
[_root_.FDRep.ofMonoidHom_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_ofMonoidHom_finrank_eq
  [Field k] [Monoid G]
  {φ : G →* k} :
-- imply
  Module.finrank k (FDRep.ofMonoidHom φ) = 1 := by
-- proof
  apply FDRep.ofMonoidHom_finrank φ

/--
[_root_.FDRep.ofMonoidHom_character](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_ofMonoidHom_character_eq
  [Field k] [Monoid G]
  {φ : G →* k} :
-- imply
  (FDRep.ofMonoidHom φ).character = φ := by
-- proof
  apply FDRep.ofMonoidHom_character φ

/--
[_root_.FDRep.ofMonoidHom_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma FDRep_ofMonoidHom_simple_eq
  [Field k] [Monoid G]
  {φ : G →* k} :
-- imply
  Simple (FDRep.ofMonoidHom φ) := by
-- proof
  apply FDRep.ofMonoidHom_simple φ

/--
[abelian_simple_char_is_hom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma abelian_simple_char_is_hom_eq
  [CommGroup G] [Finite G]
  {V : FDRep ℂ G} [Simple V] :
-- imply
  ∃ φ : G →* ℂ, V.character = ⇑φ := by
-- proof
  apply abelian_simple_char_is_hom G V

/--
[abelian_hom_is_simple_char](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma abelian_hom_is_simple_char_eq
  [CommGroup G] [Finite G]
  {φ : G →* ℂ} :
-- imply
  ∃ V : FDRep ℂ G, Simple V ∧ V.character = ⇑φ := by
-- proof
  apply abelian_hom_is_simple_char G φ

/--
[abelian_simple_iso_of_char_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean)
-/
@[path]
private lemma abelian_simple_iso_of_char_eq_eq
  [CommGroup G] [Finite G]
  {V W : FDRep ℂ G} [Simple V] [Simple W]
-- given
  (h : V.character = W.character) :
-- imply
  Nonempty (V ≅ W) := by
-- proof
  apply abelian_simple_iso_of_char_eq G V W h


-- created on 2026-10-20
