module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormEightOfFourierVanishingOrderFifteen
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 → (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | exact GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | (intros; apply GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen <;> assumption)
