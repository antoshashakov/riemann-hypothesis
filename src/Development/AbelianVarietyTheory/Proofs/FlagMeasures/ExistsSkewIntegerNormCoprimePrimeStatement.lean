module

public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewIntegerNormCoprimePrime
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.exists_skew_integer_norm_coprime_prime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ p : ℕ, p.Prime → ∃ (δ : 𝓞 E) (N : ℕ), star (δ : E) = -(δ : E) ∧ ¬ p ∣ N ∧ ∏ v, ‖φ v (δ : E)‖ ^ 2 = N := by
  first | exact @GlobalTheory.RadCov.SkewUnit.exists_skew_norm_coprime | exact GlobalTheory.RadCov.SkewUnit.exists_skew_norm_coprime | (intros; apply GlobalTheory.RadCov.SkewUnit.exists_skew_norm_coprime <;> assumption)
