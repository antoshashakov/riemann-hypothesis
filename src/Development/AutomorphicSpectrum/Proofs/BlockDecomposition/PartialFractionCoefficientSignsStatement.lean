module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSigns
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.partial_fraction_coefficient_signs : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧ ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  first | exact @GlobalTheory.CompanionTheory.RgHeSign.pfSign | exact GlobalTheory.CompanionTheory.RgHeSign.pfSign | (intros; apply GlobalTheory.CompanionTheory.RgHeSign.pfSign <;> assumption)
