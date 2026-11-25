module

public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZero
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → ValuativeRel.valuation k (t : k) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero | exact GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero | (intros; apply GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero <;> assumption)
