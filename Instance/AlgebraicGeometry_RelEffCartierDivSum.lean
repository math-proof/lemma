module
public import Mathlib.AlgebraicGeometry.Limits
public import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint
public import Theorem.Scheme.SymmetricPower
public import Abbrev.AlgebraicGeometry_RelEffCartierDivSum
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits


public section

-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_RelEffCartierDivSum.lean: instance decls only.

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)


variable {r} {T : Scheme.{u}} {g : T ⟶ S}


section Empty

variable {f}

instance RelEffCartierDiv.subsingleton_of_degree_zero : Subsingleton (RelEffCartierDiv f 0 g) :=
  ⟨fun D E => RelEffCartierDiv.ext (by rw [D.I_eq_top_of_degree_zero, E.I_eq_top_of_degree_zero])⟩

end Empty


end AlgebraicGeometry
