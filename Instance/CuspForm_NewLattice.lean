-- Carved from Lemma/Definitions/Def_CuspForm_NewLattice.lean: instance decls only.
import Def.CuspForm_IntegralStructure

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularForm

variable {M q : ℕ} [NeZero M] (A : AtkinLehnerDatum M q) (hq : q.Prime)


instance instSMulHeckeAlgebraNewLattice : SMul (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLattice A hq) :=
  ⟨fun t a => newLatticeEnd A hq t a⟩

instance instModuleHeckeAlgebraNewLattice : Module (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLattice A hq) :=
  Module.compHom (newLattice A hq) (newLatticeEnd A hq)


instance instAddCommGroupNewLatticeRed (p : ℕ) : AddCommGroup (newLatticeRed A hq p) :=
  Submodule.Quotient.addCommGroup _

instance instModuleHeckeAlgebraNewLatticeRed (p : ℕ) :
    Module (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  Submodule.Quotient.module _

instance instSMulHeckeAlgebraNewLatticeRed (p : ℕ) :
    SMul (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toDistribMulAction.toMulAction.toSMul

instance instMulActionHeckeAlgebraNewLatticeRed (p : ℕ) :
    MulAction (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toDistribMulAction.toMulAction

instance instDistribMulActionHeckeAlgebraNewLatticeRed (p : ℕ) :
    DistribMulAction (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toDistribMulAction

instance instSMulWithZeroHeckeAlgebraNewLatticeRed (p : ℕ) :
    SMulWithZero (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toMulActionWithZero.toSMulWithZero

instance instMulActionWithZeroHeckeAlgebraNewLatticeRed (p : ℕ) :
    MulActionWithZero (heckeAlgebra M 2 {ℓ | ℓ ∣ M}) (newLatticeRed A hq p) :=
  (instModuleHeckeAlgebraNewLatticeRed p).toMulActionWithZero


end CuspForm

end
