import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem.Part2
import Lemma.Fin.Eq.of.Ne_0.All_Eq


/--
[wittCancellation_independent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationIndependent.lean)
-/
@[path]
private lemma main
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
-- given
  (hSym : ∀ x y : V, B x y = B y x)
  (hNd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :
-- imply
  WittCancellationProp B :=
-- proof
  wittCancellationProp_of_symmetric B hSym hNd



-- created on 2026-10-23
-- updated on 2026-10-26
