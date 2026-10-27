import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
open DifferentialFormSpace


/--
[HamiltonianDiffeomorphism.preserves_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean)
-/
@[path]
lemma HamiltonianDiffeomorphism.preserves_symplectic
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {f : HamiltonianDiffeomorphism S} :
-- imply
  f.φ.pullback S.ω = S.ω :=
-- proof
  hamiltonian_flow_preserves_symplectic_form S f.H f.hv f.flow 1


-- created on 2026-10-23
