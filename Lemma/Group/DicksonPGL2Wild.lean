import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.DicksonPGL2Wild
open scoped BigOperators Pointwise Polynomial
open MetaMathlibExt
open Dickson


/--
[projGenLinGroup_map_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean)
-/
@[path]
private lemma projGenLinGroup_map_injective_eq
  [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
  {f : R →+* S}
-- given
  (hf : Function.Injective f) :
-- imply
  Function.Injective (Matrix.ProjGenLinGroup.map (n := by
-- proof
  apply MetaMathlibExt.Dickson.projGenLinGroup_map_injective f hf

/--
[card_projGenLinGroup_fin_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean)
-/
@[path]
private lemma card_projGenLinGroup_fin_two_eq
  [Field F] [Fintype F] :
-- imply
  Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) =
    Fintype.card F * (Fintype.card F ^ 2 - 1) := by
-- proof
  apply MetaMathlibExt.Dickson.card_projGenLinGroup_fin_two F

/--
[card_projectiveSpecialLinearGroup_fin_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean)
-/
@[path]
private lemma card_projectiveSpecialLinearGroup_fin_two_eq
  [Field F] [Fintype F]
  {p : ℕ} [CharP F p]
-- given
  (hp2 : p ≠ 2) :
-- imply
  Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
    Fintype.card F * (Fintype.card F ^ 2 - 1) / 2 := by
-- proof
  apply MetaMathlibExt.Dickson.card_projectiveSpecialLinearGroup_fin_two p F hp2

/--
[orderOf_eq_char_of_char_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean)
-/
@[path]
private lemma orderOf_eq_char_of_char_dvd_eq
  [Field F]
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] [CharP F p]
  {g : Matrix.ProjGenLinGroup (Fin 2) F}
-- given
  (hfinite : orderOf g ≠ 0)
  (hdiv : p ∣ orderOf g) :
-- imply
  orderOf g = p := by
-- proof
  apply MetaMathlibExt.Dickson.orderOf_eq_char_of_char_dvd g hfinite hdiv

/--
[classification_wild](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean)
-/
@[path]
private lemma classification_wild_eq
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
  {G : Subgroup (PGL p)} [Finite G]
-- given
  (hG_p : p ∣ Nat.card G) :
-- imply
  (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
    (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)))
    (_hφ_injective : Function.Injective φ)
    (_hφ_fixed_point_free : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v),
    Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
    Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
-- proof
  apply MetaMathlibExt.Dickson.classification_wild p G hG_p


-- created on 2026-10-20
