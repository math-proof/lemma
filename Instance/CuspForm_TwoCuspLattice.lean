module
public import Mathlib
public import Instance.CuspForm_HeckeOperatorFormsGammaH
public import Instance.FLTPrelim_Modularity
public import Theorem.CuspForm.TwoCuspLattice
public import Def.CuspForm_TwoCuspLattice
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_CuspForm_TwoCuspLattice.lean: instance decls only.

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup CohCarrier

namespace CuspForm


section Reduction

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (p : ℕ) (A : Subring ℂ) (I : Ideal A)

instance instAddCommGroupTwoCuspForms : AddCommGroup (TwoCuspForms M H k p A I) :=
  inferInstanceAs (AddCommGroup (twoCuspLattice M H k p A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p A))))

instance instModuleTwoCuspForms : Module A (TwoCuspForms M H k p A I) :=
  inferInstanceAs (Module A (twoCuspLattice M H k p A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p A))))

instance instModuleQuotientTwoCuspForms : Module (A ⧸ I) (TwoCuspForms M H k p A I) :=
  (Module.isTorsionBySet_quotient_ideal_smul (twoCuspLattice M H k p A) I).module

instance instIsScalarTowerSelfTwoCuspForms : IsScalarTower A A (TwoCuspForms M H k p A I) :=
  inferInstanceAs
    (IsScalarTower A A (twoCuspLattice M H k p A ⧸ (I • ⊤ : Submodule A (twoCuspLattice M H k p A))))

instance instIsScalarTowerTwoCuspForms : IsScalarTower A (A ⧸ I) (TwoCuspForms M H k p A I) :=
  ⟨fun a b x => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    change (a * c) • x = a • (c • x)
    exact mul_smul a c x⟩

end Reduction

end CuspForm

end
