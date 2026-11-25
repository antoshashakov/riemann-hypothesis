module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFrobeniusWindowSeriesTermMono
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  first | exact @GlobalTheory.PMonE.term_norm_mono | exact GlobalTheory.PMonE.term_norm_mono | (intros; apply GlobalTheory.PMonE.term_norm_mono <;> assumption)
