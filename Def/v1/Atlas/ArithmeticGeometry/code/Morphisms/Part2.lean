/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Theorem.v1.Atlas.ArithmeticGeometry.code.Morphisms


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- The projective vanishing set $V(S) \subseteq \mathbb{P}^n(\bar k)$ of a
family of homogeneous polynomials $S$: those points where every $f \in S$
vanishes (the rescaling identity ensures the condition descends to the
quotient). -/
def ProjVanishingSet (n : ℕ) (S : Set (HomogPoly k n)) : Set (ProjectiveSpace_k k n) :=
  {P | P.liftOn
    (fun v => ∀ f ∈ S, eval v.1 f.poly = 0)
    (by
      intro a b ⟨c, hc, hcab⟩
      simp only [eq_iff_iff]
      have ha_eq : a.1 = (fun i => c * b.1 i) := funext (hcab ·)
      constructor <;> intro h f hf
      · have heval := h f hf
        rw [show eval a.1 f.poly = c ^ f.deg * eval b.1 f.poly from by
            rw [ha_eq]; exact homog_eval_rescale k n f c b.1] at heval
        exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hc)
      · rw [show eval a.1 f.poly = c ^ f.deg * eval b.1 f.poly from by
            rw [ha_eq]; exact homog_eval_rescale k n f c b.1,
          h f hf, mul_zero])}

/-- A subset of $\mathbb{P}^n(\bar k)$ is *projectively algebraic* if it arises
as the common vanishing locus of some family of homogeneous polynomials. -/
def IsProjectiveAlgSet (n : ℕ) (V : Set (ProjectiveSpace_k k n)) : Prop :=
  ∃ S : Set (HomogPoly k n), V = ProjVanishingSet k n S

/-- The collection of all projectively algebraic subsets of $\mathbb{P}^n(\bar k)$;
its members serve as the closed sets of the projective Zariski topology. -/
def projAlgSetsCollection (n : ℕ) : Set (Set (ProjectiveSpace_k k n)) :=
  {V | IsProjectiveAlgSet k n V}

end
