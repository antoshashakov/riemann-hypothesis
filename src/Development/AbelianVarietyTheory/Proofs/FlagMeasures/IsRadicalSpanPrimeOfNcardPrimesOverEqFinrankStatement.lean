module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E → (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  first | exact @GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | exact GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | (intros; apply GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver <;> assumption)
