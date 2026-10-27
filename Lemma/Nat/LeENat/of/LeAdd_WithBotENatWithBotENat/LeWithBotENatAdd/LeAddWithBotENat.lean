import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[height_bound_from_dim_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {dim : WithBot ENat}
  {n j1 : ℕ}
-- given
  (ht : ENat)
  (h_le : dim + ht ≤ (n : WithBot ENat))
  (h_ge : (n : WithBot ENat) ≤ dim + ht)
  (h_dim : dim + (j1 : WithBot ENat) ≤ (n : WithBot ENat)) :
-- imply
  (j1 : ENat) ≤ ht := by
-- proof
  have h_eq : dim + (ht : WithBot ENat) = (n : WithBot ENat) := le_antisymm h_le h_ge
  if hdim : dim = ⊥ then
    rw [hdim, WithBot.bot_add] at h_eq
    exact absurd h_eq.symm WithBot.coe_ne_bot
  else
    obtain ⟨dim_val, rfl⟩ := WithBot.ne_bot_iff_exists.mp hdim
    if hht : ht = ⊤ then
      subst hht
      exact le_top
    else
      if hdv : dim_val = ⊤ then
        exfalso
        rw [hdv, ← WithBot.coe_add, top_add] at h_eq
        exact absurd (WithBot.coe_injective h_eq) (ENat.top_ne_natCast n)
      else
        obtain ⟨h_nat, rfl⟩ := WithTop.ne_top_iff_exists.mp hht
        obtain ⟨d_nat, rfl⟩ := WithTop.ne_top_iff_exists.mp hdv
        have h1 : (d_nat : ENat) + (h_nat : ENat) = (n : ENat) := by
          apply WithBot.coe_injective
          rwa [WithBot.coe_add]
        have h2 : (d_nat : ENat) + (j1 : ENat) ≤ (n : ENat) := by
          apply WithBot.coe_le_coe.mp
          rwa [WithBot.coe_add]
        have h1n : d_nat + h_nat = n := by
          exact_mod_cast h1
        have h2n : d_nat + j1 ≤ n := by
          exact_mod_cast h2
        exact ENat.natCast_le_natCast.mpr (show j1 ≤ h_nat by omega)


-- created on 2026-10-24
