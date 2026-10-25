/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10.Part13
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- The *degree homomorphism* `deg : [S, S] → ℤ` for a space `S` with `H_n(S) ≅ ℤ`: assigns
to each homotopy class of self-maps `[f]` the degree of the induced endomorphism of
`H_n(S)`. Multiplicative under composition. -/
def degreeHom (n : ℕ) (S : TopCat.{0})
    (φ : (homologyFunctorZ n).obj S ≅ AddCommGrpCat.of ℤ) :
    SelfMapHomotopyClass S →* ℤ where
  toFun := Quotient.lift (fun f => degreeOfEndo φ ((homologyFunctorZ n).map f))
    (fun _ _ ⟨H⟩ => by
      show degreeOfEndo φ _ = degreeOfEndo φ _
      congr 1
      exact H.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n)
  map_one' := by
    show degreeOfEndo φ ((homologyFunctorZ n).map (𝟙 S)) = 1
    rw [(homologyFunctorZ n).map_id S]; exact degreeOfEndo_id φ
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    show degreeOfEndo φ ((homologyFunctorZ n).map (_ ≫ _)) = _
    rw [(homologyFunctorZ n).map_comp]
    exact degreeOfEndo_comp φ _ _

/-- The `n`-sphere `S^n ⊆ ℝ^{n+1}` packaged as an object of `TopCat`. -/
def sphereTopCat (n : ℕ) : TopCat.{0} :=
  TopCat.of (SphereHomology.Sphere n)


/-- Safe normalization map `ℝ^{n+1} → S^n`: sends a non-zero vector `w` to `w / ‖w‖` and
maps `0` to the basepoint `e_0`, so as to be defined everywhere. -/
noncomputable def suspSafeNorm (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1))) :
    SphereHomology.Sphere n :=
  if hw : w = 0 then ⟨EuclideanSpace.single 0 1, by simp [mem_sphere_iff_norm]⟩
  else ⟨‖w‖⁻¹ • w, by
    simp [mem_sphere_iff_norm, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]⟩

/-- Project an element of `ℝ^{n+2}` onto its first `n+1` coordinates, viewed as an element
of `ℝ^{n+1}`. -/
noncomputable def suspInitProj (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (EuclideanSpace.equiv _ _).symm (fun i => v (Fin.castSucc i))

/-- Append a real scalar `t` as the last coordinate to a vector in `ℝ^{n+1}`, producing a
vector in `ℝ^{n+2}`. -/
noncomputable def suspSnocProj (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  (EuclideanSpace.equiv _ _).symm (Fin.snoc (EuclideanSpace.equiv _ _ w) t)

/-- The *raw suspension* of a self-map `f : S^n → S^n`: a map `ℝ^{n+2} → ℝ^{n+2}` that scales
the first `n+1` coordinates by `f` (after radial normalization) and leaves the last
coordinate unchanged. Restricted to `S^{n+1}` this defines the topological suspension. -/
noncomputable def suspRaw (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n)
    (v : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  suspSnocProj n
    (‖suspInitProj n v‖ • (f.1 (suspSafeNorm n (suspInitProj n v))).val)
    (v (Fin.last (n + 1)))

end BrouwerFixedPoint
