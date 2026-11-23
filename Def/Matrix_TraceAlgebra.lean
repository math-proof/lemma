module

public import Mathlib
public import Theorem.Matrix.LiftFunctor
public import Abbrev.Deformations_TraceAlgebra

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing

namespace Deformation

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

section TraceAlgebra

open ProartinianCat

variable (𝓞) in

def traceSet {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) : Set A.carrier :=
  Set.range fun g => Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier)

variable (𝓞) in

def traceSubalgebra {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) : Subalgebra 𝓞 A.carrier :=
  (Algebra.adjoin 𝓞 (traceSet 𝓞 ρ)).topologicalClosure

omit [IsLocalRing 𝓞] in
end TraceAlgebra

section TraceConj

omit [IsLocalRing 𝓞] in

end TraceConj

section Universal

open ProartinianCat

def TraceAlgebra.Descends {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) : Prop :=
  ∃ γ ∈ conjKer (n := n) A, ∀ (g : G) (i j : n),
    (((γ • ρ) g : GL n A.carrier) : Matrix n n A.carrier) i j ∈ traceSubalgebra 𝓞 ρ

end Universal

end Deformation

end
