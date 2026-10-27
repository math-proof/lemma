import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part6
open HodgeMathlib


namespace HodgeMathlib

/--
[IsElliptic.symbol_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean)
-/
@[path]
lemma IsElliptic.symbol_injective
  {n : ℕ}
  {L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)}
  {ξ : Fin n → ℝ}
  {k : ℕ}
-- given
  (hL : IsElliptic (n := n) L)
  (hξ : ξ ≠ 0) :
-- imply
  Function.Injective (principalSymbolDiffForm hL.order hL.coeff ξ (k := k)) :=
-- proof
  (hL.elliptic ξ hξ).injective

end HodgeMathlib

namespace HodgeMathlib

/--
[hodge_decomposition_three_way](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean)
-/
@[path]
lemma hodge_decomposition_three_way
  {n : ℕ}
  {cod : Codifferential n}
  {k : ℕ}
  {α : DiffForm n (k + 1)}
-- given
  (h_green : Nonempty (HasGreenOperatorDecomp (n := n) (fun α => laplacian cod α))) :
-- imply
  ∃ (h : DiffForm n (k + 1)) (β : DiffForm n k) (γ : DiffForm n (k + 2)), IsHarmonic cod h ∧ α = h + dForm β + cod.dstar γ := by
-- proof
  obtain ⟨gd⟩ := h_green
  refine ⟨gd.H α, cod.dstar (gd.G α), dForm (gd.G α), ?_, ?_⟩
  · exact gd.H_maps_to_ker α
  · have hLG := gd.LG_eq α
    show α = gd.H α + dForm (cod.dstar (gd.G α)) + cod.dstar (dForm (gd.G α))
    have hLG' : dForm (cod.dstar (gd.G α)) + cod.dstar (dForm (gd.G α)) = α + -gd.H α := hLG
    have step : gd.H α + (dForm (cod.dstar (gd.G α)) + cod.dstar (dForm (gd.G α))) = α := by
      rw [hLG']; abel
    rwa [← add_assoc] at step

end HodgeMathlib

namespace HodgeMathlib

/--
[isSmoothForm_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean)
-/
@[path]
lemma isSmoothForm_sub
  {n k : ℕ}
  {a b : DiffForm n k}
-- given
  (ha : IsSmoothForm a)
  (hb : IsSmoothForm b) :
-- imply
  IsSmoothForm (a - b) :=
-- proof
  ha.sub hb

end HodgeMathlib

namespace HodgeMathlib

/--
[elliptic_regularity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean)
-/
@[path]
lemma elliptic_regularity
  {n : ℕ}
  [sob : HasSobolevSpaces n]
  {k : ℕ}
  {ξ : DiffForm n (k + 1)}
  {s : ℕ}
-- given
  (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1))
  (param : HasParametrix (n := n) L)
  (P_preserves_smooth : ∀ {k : ℕ} (β : DiffForm n (k + 1)), IsSmoothForm β → IsSmoothForm (param.P β))
  (S_left_maps_sobolev_to_smooth : ∀ (s : ℕ) {k : ℕ} (α : DiffForm n (k + 1)), sob.IsSobolevRegular s α → IsSmoothForm (param.S_left α))
  (hξ_sob : sob.IsSobolevRegular s ξ)
  (hLξ_smooth : IsSmoothForm (L ξ)) :
-- imply
  IsSmoothForm ξ := by
-- proof
  have hid := param.PL_eq ξ
  have hP_smooth := P_preserves_smooth (L ξ) hLξ_smooth
  have hS_smooth := S_left_maps_sobolev_to_smooth s ξ hξ_sob
  have h_eq : ξ = param.P (L ξ) - param.S_left ξ := by
    rw [hid]; simp [sub_eq_add_neg, add_assoc, add_neg_cancel]
  rw [h_eq]
  exact isSmoothForm_sub _ _ hP_smooth hS_smooth

end HodgeMathlib


-- created on 2026-10-23
