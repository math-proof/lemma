import Mathlib

class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }
