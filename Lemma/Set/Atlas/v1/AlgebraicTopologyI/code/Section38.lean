import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section38.Part3
open Metric Set Manifold CategoryTheory AlgebraicTopology Limits TopCat BorsukUlam PoincareDuality
open Manifold CategoryTheory
open PoincareDuality
open CategoryTheory AlgebraicTopology Limits TopCat


namespace BorsukUlam

/--
[sphere_isConnected](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean)
-/
@[path]
lemma sphere_isConnected
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  IsConnected (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
-- proof
  isConnected_sphere (by
    apply Module.lt_rank_of_lt_finrank
    rw [finrank_euclideanSpace_fin]
    omega) 0 (by norm_num)

end BorsukUlam

namespace BorsukUlam

/--
[F2CohomRPn.instFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean)
-/
@[path]
lemma F2CohomRPn.instFree
  {n k : ℕ}
-- given
  (_hn : n ≥ 1)
  (_hk : k ≤ n) :
-- imply
  Module.Free (ZMod 2) (F2CohomRPn n k) :=
-- proof
  Module.Free.of_divisionRing (ZMod 2) (F2CohomRPn n k)

end BorsukUlam

namespace PoincareDuality

variable (R : Type) [CommRing R]
/--
[isPerfPair_compl₂](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean)
-/
@[path]
`a ⊗ b ↦ ⟨a ∪ b, [M]⟩`, before quotienting by torsion. -/
lemma isPerfPair_compl₂ {R M N N' : Type*}
  [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
  [Module R M] [Module R N] [Module R N']
  (p : M →ₗ[R] N →ₗ[R] R) (e : N' ≃ₗ[R] N)
  [hp : p.IsPerfPair] : (p.compl₂ e.toLinearMap).IsPerfPair where
  bijective_left := by
  have hbij : Function.Bijective p := hp.bijective_left
  have heq : ⇑(p.compl₂ e.toLinearMap) = (fun f : N →ₗ[R] R => f.comp e.toLinearMap) ∘ p := by
    ext m n'; simp [LinearMap.compl₂_apply]
  rw [heq]
  apply Function.Bijective.comp
  · constructor
    · intro f g h
      ext n
      have := LinearMap.ext_iff.mp h (e.symm n)
      simp at this
      exact this
    · intro f
      exact ⟨f.comp e.symm.toLinearMap, by ext n'; simp⟩
  · exact hbij
  bijective_right := by
    have hbij : Function.Bijective p.flip := hp.bijective_right
    have heq : ⇑((p.compl₂ e.toLinearMap).flip) = p.flip ∘ e := by
      ext n' m; simp [LinearMap.flip_apply, LinearMap.compl₂_apply]
    rw [heq]
    exact hbij.comp e.bijective

end PoincareDuality

/--
[isPerfPair_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean)
-/
@[path]
private lemma isPerfPair_compl_eq
  {R : Type}
  [CommRing R]
  [CommRing R]
  [AddCommGroup M]
  [AddCommGroup N]
  [AddCommGroup N']
  [Module R M]
  [Module R N]
  [Module R N']
  {p : M →ₗ[R] N →ₗ[R] R}
  {e : N' ≃ₗ[R] N}
  [hp : p.IsPerfPair] :
-- imply
  (p.compl₂ e.toLinearMap).IsPerfPair where bijective_left := by
-- proof
  apply PoincareDuality.isPerfPair_compl R p e


-- created on 2026-10-23
