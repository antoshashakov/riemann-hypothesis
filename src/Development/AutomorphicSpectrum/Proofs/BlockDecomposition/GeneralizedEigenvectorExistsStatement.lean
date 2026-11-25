module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedEigenvectorExists
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.generalized_eigenvector_exists : ∀ (Λ : Type) [Group Λ] (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Λ M), (∀ l l', ρ l * ρ l' = ρ l' * ρ l) → ∀ (U : ℕ → Subgroup Λ), Antitone U → (∀ m m', m ≤ m' → ∀ u ∈ U m, ∃ N : ℕ, 0 < N ∧ u ^ N ∈ U m') → (∀ w : M, ∃ m, ∀ u ∈ U m, ρ u w = w) → (∀ m, FiniteDimensional ℂ ↥(⨅ u : U m, LinearMap.ker (ρ (u : Λ) - 1))) → ∀ (ξ : Λ →* ℂ) (v : M), v ≠ 0 → (∀ l, v ∈ Module.End.maxGenEigenspace (ρ l) (ξ l)) → ∃ f : M →ₗ[ℂ] ℂ, f ≠ 0 ∧ ∀ l w, f (ρ l w) = ξ l * f w := by
  first | exact @GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character | exact GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character | (intros; apply GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character <;> assumption)
