/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
set_option linter.unusedSectionVars false


namespace AffineBuildingSLV

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- Two $\mathfrak{o}$-lattices $\Lambda, \Lambda'$ in $V = k^n$ are homothetic if
$\Lambda' = c \Lambda$ for some $c \in k^\times$. -/
def IsHomothetic (Λ Λ' : DVRContext.OLattice C) : Prop :=
  DVRContext.OLattice.IsHomothetic C Λ Λ'

/-- The scaled lattice $\pi \Lambda = \{\pi v : v \in \Lambda\}$ obtained by
scaling $\Lambda$ by the uniformizer $\pi$. -/
def πLattice (hπ : C.embed C.uniformizer ≠ 0)
    (Λ : DVRContext.OLattice C) : DVRContext.OLattice C where
  carrier := {v | ∃ w ∈ Λ.carrier, v = C.oscal C.uniformizer w}
  zero_mem := ⟨0, Λ.zero_mem, by funext i; simp [DVRContext.oscal]⟩
  add_mem := by
    intro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
    exact ⟨wx + wy, Λ.add_mem hwx hwy, by
      funext i; simp only [Pi.add_apply, hx, hy, DVRContext.oscal]; ring⟩
  smul_mem := by
    intro r x ⟨w, hw, hx⟩
    exact ⟨C.oscal r w, Λ.smul_mem r hw, by
      funext i; simp only [hx, DVRContext.oscal]; ring⟩
  spans_V := by
    intro v
    obtain ⟨m, cs, vs, hvs, hv⟩ := Λ.spans_V v
    refine ⟨m, fun j => cs j * (C.embed C.uniformizer)⁻¹,
            fun j => C.oscal C.uniformizer (vs j), ?_, ?_⟩
    · intro j; exact ⟨vs j, hvs j, rfl⟩
    · rw [hv]; congr 1; funext j; funext i
      simp only [Pi.smul_apply, DVRContext.oscal, smul_eq_mul]
      rw [mul_assoc, ← mul_assoc (C.embed C.uniformizer)⁻¹,
          inv_mul_cancel₀ hπ, one_mul]
  closed_under_o_combination := by
    intro coeffs vectors hcoeffs hvecs
    have hwit : ∀ i, ∃ w ∈ Λ.carrier, vectors i = C.oscal C.uniformizer w := hvecs
    choose ws hws_mem hws_eq using hwit
    have hsum : ∑ i, coeffs i • vectors i =
        C.oscal C.uniformizer (∑ i, coeffs i • ws i) := by
      simp only [hws_eq]; funext j
      simp only [DVRContext.oscal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [hsum]
    exact ⟨∑ i, coeffs i • ws i,
           Λ.closed_under_o_combination coeffs ws hcoeffs hws_mem, rfl⟩

/-- Incidence of $\mathfrak{o}$-lattices: $y \subseteq x$ and
$\pi x \subseteq y$. This makes $x/y$ an $\mathfrak{o}/\mathfrak{m}$-vector
space, encoding the simplicial relation in the Bruhat-Tits building. -/
def OLattice.IsIncident (x y : DVRContext.OLattice C) : Prop :=
  y.carrier ⊆ x.carrier ∧ ∀ v ∈ x.carrier, C.oscal C.uniformizer v ∈ y.carrier

/-- Incidence relation on homothety classes: two classes $[\Lambda], [\Lambda']$
are incident if they are equal or have representatives $x \in [\Lambda]$,
$y \in [\Lambda']$ that are incident in the lattice sense. -/
def IncidenceRel (ξ η : DVRContext.HomothetyClass C) : Prop :=
  ξ = η ∨
  ∃ x y : DVRContext.OLattice C,
    Quot.mk _ x = ξ ∧ Quot.mk _ y = η ∧ OLattice.IsIncident C x y

end AffineBuildingSLV
