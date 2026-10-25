import Mathlib
import Abbrev.GroupCohomology_TateCohomology
import Lemma.GroupCohomology.TateSeam

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def tateMap {A B : Rep.{u} k G} (φ : A ⟶ B) : ∀ n : ℤ, (A.tateCohomology n ⟶ B.tateCohomology n)
  | (Int.ofNat (n + 1)) => groupCohomology.map (MonoidHom.id G) φ (n + 1)
  | (Int.ofNat 0) => ModuleCat.ofHom (tateH0Map φ)
  | (Int.negSucc 0) => ModuleCat.ofHom (tateHneg1Map φ)
  | (Int.negSucc (n + 1)) => groupHomology.map (MonoidHom.id G) φ (n + 1)


variable {X : ShortComplex (Rep.{u} k G)}

def tateδ (hX : X.ShortExact) : ∀ n : ℤ, (X.X₃.tateCohomology n ⟶ X.X₁.tateCohomology (n + 1))
  | (Int.ofNat (n + 1)) => groupCohomology.δ hX (n + 1) (n + 2) rfl
  | (Int.ofNat 0) => ModuleCat.ofHom (tateδ₀ hX)
  | (Int.negSucc 0) => ModuleCat.ofHom (tateδneg1 hX)
  | (Int.negSucc 1) => ModuleCat.ofHom (tateδneg2 hX)
  | (Int.negSucc (n + 2)) => groupHomology.δ hX (n + 2) (n + 1) rfl

end Rep

end
