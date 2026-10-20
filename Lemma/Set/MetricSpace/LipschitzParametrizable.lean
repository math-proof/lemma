import Mathlib
import sympy.Basic
import sympy.atlas.Topology.MetricSpace.LipschitzParametrizable
open Finset
open Set


/--
[unitCube_zero_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
private lemma unitCube_zero_mem_eq
  {d : ℕ} :
-- imply
  (0 : Fin d → ℝ) ∈ unitCube d := by
-- proof
  apply unitCube_zero_mem d

/--
[isLipschitzParametrizable_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
private lemma isLipschitzParametrizable_empty_eq
  [MetricSpace X]
  {d : ℕ} :
-- imply
  IsLipschitzParametrizable d (∅ : Set X) := by
-- proof
  apply isLipschitzParametrizable_empty d

/--
[isLipschitzParametrizable_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
private lemma isLipschitzParametrizable_singleton_eq
  [MetricSpace X]
  {d : ℕ}
  {x : X} :
-- imply
  IsLipschitzParametrizable d ({x} : Set X) := by
-- proof
  apply isLipschitzParametrizable_singleton d x

/--
[isLipschitzParametrizable_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
private lemma isLipschitzParametrizable_coe_eq
  [MetricSpace X]
  {d : ℕ}
  {s : Finset X} :
-- imply
  IsLipschitzParametrizable d (↑s : Set X) := by
-- proof
  apply Finset.isLipschitzParametrizable_coe d s

/--
[Finite.isLipschitzParametrizable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
private lemma Finite_isLipschitzParametrizable_eq
  [MetricSpace X]
  {B : Set X}
  {d : ℕ}
-- given
  (hB : B.Finite) :
-- imply
  IsLipschitzParametrizable d B := by
-- proof
  apply Set.Finite.isLipschitzParametrizable hB d

/--
[IsLipschitzParametrizable.image_lipschitzWith](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/LipschitzParametrizable.lean)
-/
@[path]
private lemma IsLipschitzParametrizable_image_lipschitzWith_eq
  [MetricSpace X] [MetricSpace Y]
  {d : ℕ}
  {B : Set X}
  {f : X → Y}
  {K : NNReal}
-- given
  (hB : IsLipschitzParametrizable d B)
  (hf : LipschitzWith K f) :
-- imply
  IsLipschitzParametrizable d (f '' B) := by
-- proof
  apply IsLipschitzParametrizable.image_lipschitzWith hB hf


-- created on 2026-10-20
