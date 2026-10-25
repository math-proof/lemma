import Mathlib

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace groupCohomology
namespace Cores

section Transversal
variable {G : Type} [Group G] (H : Subgroup G)

structure Transversal where
  σ : G ⧸ H → G
  mk_σ : ∀ q, (σ q : G ⧸ H) = q
  σ_one : σ ((1 : G) : G ⧸ H) = 1

namespace Transversal
variable {H}


variable (τ : Transversal H)


end Transversal

end Transversal

section Cor
variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)


end Cor
end Cores

/-- Re-declare at `groupCohomology` root so `open groupCohomology` + Fin CorFin attribute resolves. -/
@[reducible, instance] noncomputable def fintypeQuot {G : Type} [Group G] {H : Subgroup G}
    [H.FiniteIndex] : Fintype (G ⧸ H) :=
  Cores.fintypeQuot (H := H)

end groupCohomology
