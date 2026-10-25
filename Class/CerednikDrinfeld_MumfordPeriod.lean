import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

namespace CerednikDrinfeld
namespace Mumford

class GraphAction (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) : Prop where
  smul_adj : ∀ (g : G) {v w : W}, 𝒯.Adj v w → 𝒯.Adj (g • v) (g • w)

end Mumford
end CerednikDrinfeld
