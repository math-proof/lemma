import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.CharacterOrthogonality
open CategoryTheory
open BurnsidePaqb


/--
[simple_fdrep_of_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma simple_fdrep_of_irreducible_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Finite G]
  {σ : Representation ℂ G V} [σ.IsIrreducible] :
-- imply
  Simple (FDRep.of σ) := by
-- proof
  apply BurnsidePaqb.simple_fdrep_of_irreducible G σ

/--
[irreducible_of_simple_fdrep_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma irreducible_of_simple_fdrep_aux_eq
  [Group G] [Fintype G] [Finite G]
  {V : FDRep ℂ G} [Simple V]
  {σ : Representation ℂ G V}
-- given
  (hσ : (V.ρ : Representation ℂ G V) = σ) :
-- imply
  σ.IsIrreducible := by
-- proof
  apply BurnsidePaqb.irreducible_of_simple_fdrep_aux G V σ hσ

/--
[irreducible_of_simple_fdrep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma irreducible_of_simple_fdrep_eq
  [Group G] [Fintype G] [Finite G]
  {V : FDRep ℂ G} [Simple V] :
-- imply
  Representation.IsIrreducible (V.ρ : Representation ℂ G V) := by
-- proof
  apply BurnsidePaqb.irreducible_of_simple_fdrep G V

/--
[Irr.charFun_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_charFun_mk_eq
  [Group G] [Fintype G]
  {S : {V : FDRep ℂ G // Simple V}} :
-- imply
  Irr.charFun G (Quotient.mk _ S) = S.1.character := by
-- proof
  apply BurnsidePaqb.Irr.charFun_mk G S

/--
[Irr.mk_repBundle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_mk_repBundle_eq
  [Group G] [Fintype G]
  {c : Irr G} :
-- imply
  Quotient.mk _ (Irr.repBundle G c) = c := by
-- proof
  apply BurnsidePaqb.Irr.mk_repBundle G c

/--
[Irr.charFun_repBundle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_charFun_repBundle_eq
  [Group G] [Fintype G]
  {c : Irr G} :
-- imply
  (Irr.repBundle G c).1.character = Irr.charFun G c := by
-- proof
  apply BurnsidePaqb.Irr.charFun_repBundle G c

/--
[Irr.charFun_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_charFun_inj_eq
  [Group G] [Fintype G] [Finite G] :
-- imply
  Function.Injective (Irr.charFun G) := by
-- proof
  apply BurnsidePaqb.Irr.charFun_inj G

/--
[Irr.charFun_triv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_charFun_triv_eq
  [Group G] [Fintype G]
  {g : G} :
-- imply
  Irr.charFun G (Irr.triv G) g = 1 := by
-- proof
  apply BurnsidePaqb.Irr.charFun_triv G g

/--
[Irr.charFun_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_charFun_one_eq
  [Group G] [Fintype G]
  {c : Irr G} :
-- imply
  Irr.charFun G c 1 = ((Module.finrank ℂ ↥(Irr.repBundle G c).1 : ℕ) : ℂ) := by
-- proof
  apply BurnsidePaqb.Irr.charFun_one G c

/--
[Irr.charFun_eq_repBundle_char](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_charFun_eq_repBundle_char_eq
  [Group G] [Fintype G]
  {c : Irr G}
  {x : G} :
-- imply
  Irr.charFun G c x = Representation.character
    ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1) x := by
-- proof
  apply BurnsidePaqb.Irr.charFun_eq_repBundle_char G c x

/--
[charInner_orth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma charInner_orth_eq
  [Group G] [Fintype G]
  {i j : Irr G} :
-- imply
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, Irr.charFun G i g * Irr.charFun G j g⁻¹ =
    if i = j then 1 else 0 := by
-- proof
  apply BurnsidePaqb.charInner_orth G i j

/--
[cardBound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma cardBound_eq
  [Group G] [Fintype G]
  {s : Finset (Irr G)} :
-- imply
  s.card ≤ Fintype.card G := by
-- proof
  apply BurnsidePaqb.cardBound G s

/--
[zimmOp_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma zimmOp_comm_eq
  [Group G] [Fintype G] [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M] [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
  {f : G → ℂ}
  {x : M}
-- given
  (hf : IsClassFun G f)
  (h : G) :
-- imply
  (Representation.ofModule' (k := by
-- proof
  apply BurnsidePaqb.zimmOp_comm G M f hf h x

/--
[irreducible_ofModule'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma irreducible_ofModule'_eq
  [Group G] [Fintype G] [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M] [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [IsSimpleModule (MonoidAlgebra ℂ G) M] :
-- imply
  (Representation.ofModule' (k := by
-- proof
  apply BurnsidePaqb.irreducible_ofModule' G M

/--
[zimmEigenScalar](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma zimmEigenScalar_eq
  [Group G] [Fintype G] [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M] [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [Module.Finite ℂ M] [IsSimpleModule (MonoidAlgebra ℂ G) M]
  {f : G → ℂ}
-- given
  (hf : IsClassFun G f) :
-- imply
  ∃ μ : ℂ, ∀ y : M, zimmOp G M f y = μ • y := by
-- proof
  apply BurnsidePaqb.zimmEigenScalar G M f hf

/--
[zimmVanish](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma zimmVanish_eq
  [Group G] [Fintype G] [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M] [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [Module.Finite ℂ M] [IsSimpleModule (MonoidAlgebra ℂ G) M]
  {f : G → ℂ}
-- given
  (hf : IsClassFun G f)
  (horth : ∀ c : Irr G, (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹ = 0) :
-- imply
  zimmOp G M f = 0 := by
-- proof
  apply BurnsidePaqb.zimmVanish G M f hf horth

/--
[ofModule'_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma ofModule'_apply_eq
  [Group G] [Fintype G] [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M] [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
  {g : G}
  {x : M} :
-- imply
  (Representation.ofModule' (k := by
-- proof
  apply BurnsidePaqb.ofModule'_apply G M g x

/--
[zimmKerStab](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma zimmKerStab_eq
  [Group G] [Fintype G]
  {f : G → ℂ}
  {a : MonoidAlgebra ℂ G}
-- given
  (hf : IsClassFun G f) :
-- imply
  ∀ (x : RegMod G) (_ : zimmOp G (RegMod G) f x = 0),
    zimmOp G (RegMod G) f (a • x) = 0 := by
-- proof
  apply BurnsidePaqb.zimmKerStab G f hf a

/--
[zimmTopVanish](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma zimmTopVanish_eq
  [Group G] [Fintype G]
  {f : G → ℂ}
-- given
  (hf : IsClassFun G f)
  (horth : ∀ c : Irr G, (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹ = 0) :
-- imply
  zimmOp G (RegMod G) f = 0 := by
-- proof
  apply BurnsidePaqb.zimmTopVanish G hf horth

/--
[classfun_eq_zero_of_orth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma classfun_eq_zero_of_orth_eq
  [Group G] [Fintype G]
  {f : G → ℂ}
-- given
  (hf : IsClassFun G f)
  (horth : ∀ c : Irr G, (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹ = 0) :
-- imply
  f = 0 := by
-- proof
  apply BurnsidePaqb.classfun_eq_zero_of_orth G hf horth

/--
[Irr.charFun_classfun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma Irr_charFun_classfun_eq
  [Group G] [Fintype G]
  {c : Irr G}
  {g h : G} :
-- imply
  Irr.charFun G c (h * g * h⁻¹) = Irr.charFun G c g := by
-- proof
  apply BurnsidePaqb.Irr.charFun_classfun G c g h

/--
[classfun_expand](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma classfun_expand_eq
  [Group G] [Fintype G]
  {f : G → ℂ}
-- given
  (hf : IsClassFun G f) :
-- imply
  f = ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) •
    Irr.charFun G c := by
-- proof
  apply BurnsidePaqb.classfun_expand G hf

/--
[deltaOne_classfun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma deltaOne_classfun_eq
  [Group G] [Fintype G] :
-- imply
  IsClassFun G (deltaOne G) := by
-- proof
  apply BurnsidePaqb.deltaOne_classfun G

/--
[deltaOne_inner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma deltaOne_inner_eq
  [Group G] [Fintype G]
  {c : Irr G} :
-- imply
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, deltaOne G g * Irr.charFun G c g⁻¹ =
    (Nat.card G : ℂ)⁻¹ * Irr.charFun G c 1 := by
-- proof
  apply BurnsidePaqb.deltaOne_inner G c

/--
[regular_character_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma regular_character_vanishes_eq
  [Group G] [Fintype G]
  {g : G}
-- given
  (hg : g ≠ 1) :
-- imply
  ∑ c : Irr G, Irr.charFun G c 1 * Irr.charFun G c g = 0 := by
-- proof
  apply BurnsidePaqb.regular_character_vanishes G g hg

/--
[sum_deg_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean)
-/
@[path]
private lemma sum_deg_sq_eq
  [Group G] [Fintype G] :
-- imply
  ∑ c : Irr G, (Irr.charFun G c 1) ^ 2 = (Fintype.card G : ℂ) := by
-- proof
  apply BurnsidePaqb.sum_deg_sq G


-- created on 2026-10-20
