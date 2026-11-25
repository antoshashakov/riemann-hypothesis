module

public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelDensitiesOfHermitianForm
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.siegel_densities_of_hermitian_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SiegelDensities F E σ M J := by
  first | exact @GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities | exact GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities | (intros; apply GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities <;> assumption)
