module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCountBound
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal

theorem _root_.GlobalTheory.T.fundamental_domain_integral_count_bound : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (M : Set G), MeasurableSet M → ∀ (f : G → ℝ≥0∞), Measurable f →
    (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → ∀ n : ℕ, (∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) →
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | exact GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | (intros; apply GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le <;> assumption)
