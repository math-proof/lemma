import Mathlib

open Filter Topology Complex
open scoped Real ComplexConjugate

noncomputable section


def eisensteinScattering (s : ℂ) : ℂ :=
  completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)


def CompletedZetaConjSymm : Prop :=
  ∀ s : ℂ, completedRiemannZeta (conj s) = conj (completedRiemannZeta s)

end
