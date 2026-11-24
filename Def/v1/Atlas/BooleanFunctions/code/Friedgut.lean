module
public import Def.v1.Atlas.BooleanFunctions.code.FKN
public import Def.v1.Atlas.BooleanFunctions.code.Influence
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Influence
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.MonotoneFourier
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Stability
public import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
public import Def.v1.Atlas.BooleanFunctions.code.MonotoneFourier
public import Def.v1.Atlas.BooleanFunctions.code.Stability
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Friedgut.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

def IsBoolFnJunta {n : ℕ} (g : (Fin n → Bool) → Bool) (J : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ J ∧
    ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → g x = g y

noncomputable def boolL2Dist {n : ℕ} (f g : (Fin n → Bool) → Bool) : ℝ :=
  lpNorm 2 (fun x => liftPM f x - liftPM g x)

def restrictToCoords {n : ℕ} (f : (Fin n → Bool) → Bool)
    (J : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => f (fun i => if i ∈ J then x i else false)

open Real Finset in
noncomputable def fourierTrunc {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (J : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (· ⊆ J),
    fourierCoeff f S * chi S x

noncomputable def fourierTruncBool {n : ℕ} (f : (Fin n → Bool) → Bool)
    (J : Finset (Fin n)) : (Fin n → Bool) → Bool :=
  fun x => if (0 : ℝ) ≤ fourierTrunc (liftPM f) J x then true else false

end BooleanFourier
