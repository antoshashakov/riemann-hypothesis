module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalization
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization : ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) → IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  first | exact @GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | exact GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | (intros; apply GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away <;> assumption)
