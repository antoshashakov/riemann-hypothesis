module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdeal
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.twist_isMultiHomogIdeal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), IsMultiHomogIdeal W → IsMultiHomogIdeal (twist p W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist <;> assumption)
