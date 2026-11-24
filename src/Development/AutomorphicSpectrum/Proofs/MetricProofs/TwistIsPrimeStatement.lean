module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrime
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → NoRoot p W → (twist p W).IsPrime := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | exact GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime <;> assumption)
