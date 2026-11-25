module

import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.RowsStackRight
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenExists

@[expose] public section

namespace GlobalTheory.NatMulIntegralNsmul

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ M : ℕ, 0 < M ∧ IsIntegral ℤ ((M : E) * a) := GlobalTheory.DenominatorExistence.den_exists a

theorem exists_nsmul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (h : Submodule.IsFullLattice E Λ)
    (v : Fin n → E) : ∃ (N : ℕ), (0 : ℕ) < N ∧ N • v ∈ Λ := by
  apply PositivityTheory.ThKW.exists_nsmul_mem <;> assumption

end GlobalTheory.NatMulIntegralNsmul
