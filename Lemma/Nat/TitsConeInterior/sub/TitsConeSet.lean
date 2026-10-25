import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeInterior
open Finset BigOperators CoxeterGroup TitsCone


namespace Definitions
end Definitions
namespace TitsCone

/--
[titsConeInterior_subset_titsCone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeInterior.lean)
-/
@[path]
private lemma titsConeInterior_subset_titsCone
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  titsConeInterior M ⊆ titsConeSet M := by
-- proof
  intro x hx
  obtain ⟨y, hy, ws, rfl⟩ := hx
  exact ⟨y, fun s => le_of_lt (hy s), ws, rfl⟩

end TitsCone

namespace TitsCone

/--
[titsCone_interior_iff_open_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeInterior.lean)
-/
@[path]
private lemma titsCone_interior_iff_open_chamber
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {x : B → ℝ}
-- given
  (hx : x ∈ titsConeSet M) :
-- imply
  x ∈ titsConeInterior M ↔ ∀ (ws : List B) (y : B → ℝ), y ∈ titsFundamentalClosure M → x = wordAction M ws y → y ∈ titsFundamentalChamber M := by
-- proof
  constructor
  ·
    intro ⟨y₀, hy₀, ws₀, hx_eq⟩ ws y hy hxy
    have hy₀_cl : y₀ ∈ titsFundamentalClosure M := fun s => le_of_lt (hy₀ s)
    have heq : wordAction M ws y = wordAction M ws₀ y₀ := hxy.symm.trans hx_eq
    have hcomb : wordAction M (ws₀ ++ ws.reverse) y₀ = y := by
      rw [wordAction_append, ← heq, wordAction_reverse_cancel]
    have : y = y₀ := fundamental_domain_uniqueness M y y₀ hy hy₀_cl
      (ws₀ ++ ws.reverse) hcomb
    rwa [this]
  ·
    intro h
    obtain ⟨y, hy, ws, rfl⟩ := hx
    exact ⟨y, h ws y hy rfl, ws, rfl⟩

end TitsCone


-- created on 2026-10-24
