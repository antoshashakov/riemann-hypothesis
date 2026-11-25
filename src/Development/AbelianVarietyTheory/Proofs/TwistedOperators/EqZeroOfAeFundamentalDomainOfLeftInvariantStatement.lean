module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariant
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ F : G → ℂ, Continuous F → (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) → ∀ x, F x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | exact GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | (intros; apply GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant <;> assumption)
