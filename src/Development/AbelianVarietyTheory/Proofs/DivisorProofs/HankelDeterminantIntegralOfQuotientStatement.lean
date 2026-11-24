module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HankelDeterminantIntegralOfQuotient
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.hankelDeterminant_integral_of_quotient : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  first | exact @GlobalTheory.Nef.hankel_integral | exact GlobalTheory.Nef.hankel_integral | (intros; apply GlobalTheory.Nef.hankel_integral <;> assumption)
