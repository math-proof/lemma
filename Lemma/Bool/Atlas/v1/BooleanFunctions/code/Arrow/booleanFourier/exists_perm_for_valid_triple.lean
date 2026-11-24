import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.exists_perm_placing_at_positions
open BooleanFourier Bool


/--
[exists_perm_for_valid_triple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {a b c : Fin m}
  {pab pbc pac : Bool}
-- given
  (hm : m ≥ 3)
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c)
  (hvalid : pab = pbc → pac = pab) :
-- imply
  ∃ σ : Equiv.Perm (Fin m), prefersOver σ a b = pab ∧ prefersOver σ b c = pbc ∧ prefersOver σ a c = pac := by
-- proof
  have hba := hab.symm; have hcb := hbc.symm; have hca := hac.symm
  match pab, pbc, pac, hvalid with
  | true, true, true, _ =>
    obtain ⟨σ, hσa, hσb, hσc⟩ := exists_perm_placing_at_positions (a := a) (b := b) (c := c) hm hab hbc hac
    exact ⟨σ, prefersOver_of_lt (by rw [hσa, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
      prefersOver_of_lt (by rw [hσb, hσc]; exact Fin.mk_lt_mk.mpr (by omega)),
      prefersOver_of_lt (by rw [hσa, hσc]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | true, false, true, _ =>
    obtain ⟨σ, hσa, hσc, hσb⟩ := exists_perm_placing_at_positions (a := a) (b := c) (c := b) hm hac hcb hab
    exact ⟨σ, prefersOver_of_lt (by rw [hσa, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
      not_prefersOver_of_lt (by rw [hσc, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
      prefersOver_of_lt (by rw [hσa, hσc]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | false, true, true, _ =>
    obtain ⟨σ, hσb, hσa, hσc⟩ := exists_perm_placing_at_positions (a := b) (b := a) (c := c) hm hba hac hbc
    exact ⟨σ, not_prefersOver_of_lt (by rw [hσb, hσa]; exact Fin.mk_lt_mk.mpr (by omega)),
      prefersOver_of_lt (by rw [hσb, hσc]; exact Fin.mk_lt_mk.mpr (by omega)),
      prefersOver_of_lt (by rw [hσa, hσc]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | false, true, false, _ =>
    obtain ⟨σ, hσb, hσc, hσa⟩ := exists_perm_placing_at_positions (a := b) (b := c) (c := a) hm hbc hca hba
    exact ⟨σ, not_prefersOver_of_lt (by rw [hσb, hσa]; exact Fin.mk_lt_mk.mpr (by omega)),
      prefersOver_of_lt (by rw [hσb, hσc]; exact Fin.mk_lt_mk.mpr (by omega)),
      not_prefersOver_of_lt (by rw [hσc, hσa]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | true, false, false, _ =>
    obtain ⟨σ, hσc, hσa, hσb⟩ := exists_perm_placing_at_positions (a := c) (b := a) (c := b) hm hca hab hcb
    exact ⟨σ, prefersOver_of_lt (by rw [hσa, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
      not_prefersOver_of_lt (by rw [hσc, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
      not_prefersOver_of_lt (by rw [hσc, hσa]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | false, false, false, _ =>
    obtain ⟨σ, hσc, hσb, hσa⟩ := exists_perm_placing_at_positions (a := c) (b := b) (c := a) hm hcb hba hca
    exact ⟨σ, not_prefersOver_of_lt (by rw [hσb, hσa]; exact Fin.mk_lt_mk.mpr (by omega)),
      not_prefersOver_of_lt (by rw [hσc, hσb]; exact Fin.mk_lt_mk.mpr (by omega)),
      not_prefersOver_of_lt (by rw [hσc, hσa]; exact Fin.mk_lt_mk.mpr (by omega))⟩
  | true, true, false, h => exact absurd (h rfl) Bool.noConfusion
  | false, false, true, h => exact absurd (h rfl) Bool.noConfusion


lemma BooleanFourier.exists_perm_for_valid_triple
  {m : ℕ}
  {a b c : Fin m}
  {pab pbc pac : Bool}
-- given
  (hm : m ≥ 3)
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c)
  (hvalid : pab = pbc → pac = pab) :
-- imply
  ∃ σ : Equiv.Perm (Fin m), prefersOver σ a b = pab ∧ prefersOver σ b c = pbc ∧ prefersOver σ a c = pac :=
-- proof
  main hm hab hbc hac hvalid


-- created on 2026-10-23
-- updated on 2026-11-24
