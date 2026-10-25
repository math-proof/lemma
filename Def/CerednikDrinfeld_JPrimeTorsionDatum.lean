import Def.CerednikDrinfeld_Ribbon
import Def.HeckeGalois_EichlerShimura
import Lemma.Compat.Mathlib430
import Structure.CerednikDrinfeld_JPrimeTorsionDatum

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve


namespace JPrimeTorsionDatum

variable {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {A : ValuationSubring (AlgebraicClosure ℚ)}

noncomputable def invariants (Dm : JPrimeTorsionDatum p E V A) : AddSubgroup Dm.T :=
  ⨅ σ ∈ A.inertiaSubgroupIn ℚ, ((Dm.gal σ).toAddMonoidHom - AddMonoidHom.id Dm.T).ker

noncomputable def W (Dm : JPrimeTorsionDatum p E V A) (𝔪 : Ideal HeckeAlg) : AddSubgroup Dm.T :=
  ⨅ x ∈ 𝔪, (Dm.hecke x).toAddMonoidHom.ker

end JPrimeTorsionDatum

end CerednikDrinfeld
