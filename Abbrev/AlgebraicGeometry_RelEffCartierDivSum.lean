import Mathlib.AlgebraicGeometry.Limits
import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint
import Structure.AlgebraicCurve_SymmetricPower

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)

noncomputable abbrev fibrePowOver : Scheme.{u} :=
  widePullback S (fun _ : Fin r => 𝒞) (fun _ => f)

namespace fibrePowOver

noncomputable abbrev proj (i : Fin r) : fibrePowOver f r ⟶ 𝒞 :=
  WidePullback.π (fun _ : Fin r => f) i

noncomputable abbrev toBase : fibrePowOver f r ⟶ S :=
  WidePullback.base (fun _ : Fin r => f)

@[reassoc (attr := simp)]
theorem proj_comp (i : Fin r) : proj f r i ≫ f = toBase f r :=
  WidePullback.π_arrow _ _

end fibrePowOver

variable {r} {T : Scheme.{u}} {g : T ⟶ S}


namespace SameDivisor

variable {f}


end SameDivisor

section Empty


end Empty

namespace fibrePowOver

variable (r)


end fibrePowOver

section FieldComparison

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)


end FieldComparison

end AlgebraicGeometry
