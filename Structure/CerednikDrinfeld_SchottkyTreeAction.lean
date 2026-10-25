import Class.CerednikDrinfeld_MumfordPeriod
import Mathlib.Algebra.Group.Action.Faithful

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open MulAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

variable (G) in

structure IsTreeLattice : Prop where

  faithful : FaithfulSMul G W

  finite_stabilizer : ∀ w : W, Finite (stabilizer G w)

  finite_quotVert : Finite (QuotVert G W)

  finite_quotEdge : Finite (QuotEdge G 𝒯)

variable (G) in

structure IsSchottky : Prop where

  stabilizer_eq_bot : ∀ w : W, stabilizer G w = ⊥

  smul_ne_symm : ∀ (g : G) (d : 𝒯.Dart), g • d ≠ d.symm

  finite_quotVert : Finite (QuotVert G W)

  finite_quotEdge : Finite (QuotEdge G 𝒯)


namespace IsSchottky

variable {𝒯}


end IsSchottky

namespace IsTreeLattice

variable {𝒯}


end IsTreeLattice


variable {𝒯} in


variable {𝒯} in


open scoped Classical in


section lemmas

variable [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯)


end lemmas

end Mumford
end CerednikDrinfeld

end
