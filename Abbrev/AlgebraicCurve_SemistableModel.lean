import Mathlib
import Structure.AlgebraicCurve_SemistableCharts
import Instance.AlgebraicCurve_SemistableModel
import Structure.AlgebraicCurve_SemistableModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w u₁ u₂

namespace AlgebraicCurve

namespace SemistableModel


end SemistableModel

variable {L : Type u} [Field L] (A : ValuationSubring L)
variable (F : Type v) [Field F] [Algebra L F]
variable {ιV : Type u₁} {ιE : Type u₂} (Fbar : ιV → Type w) [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
variable (C : ∀ i, ComponentChart A F (Fbar i)) (An : ιE → Annulus A F) (src tgt : ιE → ιV)
variable (xs : ∀ e, Place (ResidueField A) (Fbar (src e))) (xt : ∀ e, Place (ResidueField A) (Fbar (tgt e)))


namespace SemistableModel

variable {A F Fbar C An src tgt xs xt}

abbrev closedPointι (A : ValuationSubring L) :
    Spec (CommRingCat.of (ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))


end SemistableModel

end AlgebraicCurve

end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w u₁ u₂

namespace AlgebraicCurve


variable {L : Type u} [Field L] (A : ValuationSubring L)
variable (F : Type v) [Field F] [Algebra L F]
variable {ιV : Type u₁} {ιE : Type u₂} (Fbar : ιV → Type w) [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
variable (C : ∀ i, ComponentChart A F (Fbar i)) (An : ιE → Annulus A F) (src tgt : ιE → ιV)
variable (xs : ∀ e, Place (ResidueField A) (Fbar (src e))) (xt : ∀ e, Place (ResidueField A) (Fbar (tgt e)))


namespace SemistableModel

variable {A F Fbar C An src tgt xs xt}


abbrev closedFibre (M : SemistableModel A F Fbar C An src tgt xs xt) : Scheme.{u} :=
  Limits.pullback M.toBase (closedPointι A)

abbrev closedFibreι (M : SemistableModel A F Fbar C An src tgt xs xt) : M.closedFibre ⟶ M.X :=
  Limits.pullback.fst M.toBase (closedPointι A)


abbrev Descent.closedFibre₀ {M : SemistableModel A F Fbar C An src tgt xs xt} (D : M.Descent) : Scheme.{u} :=
  Limits.pullback D.toBase₀ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D.A₀)))

end SemistableModel

end AlgebraicCurve

end
