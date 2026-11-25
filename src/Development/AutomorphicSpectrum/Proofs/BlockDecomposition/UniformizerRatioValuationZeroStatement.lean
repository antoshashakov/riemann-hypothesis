module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZero
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.ConjugateSelfDual.Statement

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

theorem _root_.GlobalTheory.T.uniformizer_ratio_valuation_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) → GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | exact GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero <;> assumption)
