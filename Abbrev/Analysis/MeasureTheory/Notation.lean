import Mathlib


/-!
# Introduction to Measure Theory, Chapter 0: Notation

A companion to Chapter 0 of the book "An introduction to Measure Theory".

We use existing Mathlib constructions, such as {name}`Set.indicator`, {name}`EuclideanSpace`, {name}`ENNReal`,
and {name}`tsum` to describe the concepts defined in Chapter 0.

-/

/-- A version of {name}`Set.indicator` suitable for this text. -/
noncomputable abbrev Set.indicator' {X: Type*} (E: Set X) := indicator E (fun _ ↦ (1:ℝ))

