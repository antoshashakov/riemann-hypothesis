module

public import Formalism.RealPlaceAnalysis.Complexify
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilator
import Supplements.MathlibImports.AnalysisAndTactics
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.commutator_coercive_on_annihilator : ∀ {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ), (∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) → ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 → Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | exact GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator <;> assumption)
