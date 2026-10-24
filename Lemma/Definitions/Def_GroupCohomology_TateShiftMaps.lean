import Mathlib
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateSeam

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

lemma tateMap_ofNat_succ {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    tateMap φ (n + 1 : ℕ) = groupCohomology.map (MonoidHom.id G) φ (n + 1) := rfl
lemma tateMap_zero {A B : Rep.{u} k G} (φ : A ⟶ B) : tateMap φ 0 = ModuleCat.ofHom (tateH0Map φ) := rfl
lemma tateMap_neg_one {A B : Rep.{u} k G} (φ : A ⟶ B) : tateMap φ (-1) = ModuleCat.ofHom (tateHneg1Map φ) := rfl
lemma tateMap_negSucc_succ {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    tateMap φ (Int.negSucc (n + 1)) = groupHomology.map (MonoidHom.id G) φ (n + 1) := rfl

variable {X : ShortComplex (Rep.{u} k G)}

def tateδ (hX : X.ShortExact) : ∀ n : ℤ, (X.X₃.tateCohomology n ⟶ X.X₁.tateCohomology (n + 1))
  | (Int.ofNat (n + 1)) => groupCohomology.δ hX (n + 1) (n + 2) rfl
  | (Int.ofNat 0) => ModuleCat.ofHom (tateδ₀ hX)
  | (Int.negSucc 0) => ModuleCat.ofHom (tateδneg1 hX)
  | (Int.negSucc 1) => ModuleCat.ofHom (tateδneg2 hX)
  | (Int.negSucc (n + 2)) => groupHomology.δ hX (n + 2) (n + 1) rfl

lemma tateδ_ofNat_succ (hX : X.ShortExact) (n : ℕ) : tateδ hX (n + 1 : ℕ) = groupCohomology.δ hX (n + 1) (n + 2) rfl := rfl
lemma tateδ_zero (hX : X.ShortExact) : tateδ hX 0 = ModuleCat.ofHom (tateδ₀ hX) := rfl
lemma tateδ_neg_one (hX : X.ShortExact) : tateδ hX (-1) = ModuleCat.ofHom (tateδneg1 hX) := rfl
lemma tateδ_neg_two (hX : X.ShortExact) : tateδ hX (-2) = ModuleCat.ofHom (tateδneg2 hX) := rfl
lemma tateδ_negSucc_succ_succ (hX : X.ShortExact) (n : ℕ) :
    tateδ hX (Int.negSucc (n + 2)) = groupHomology.δ hX (n + 2) (n + 1) rfl := rfl

end Rep

end
