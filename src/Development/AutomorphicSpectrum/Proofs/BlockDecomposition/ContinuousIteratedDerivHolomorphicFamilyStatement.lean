module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIteratedDerivHolomorphicFamily
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Topology Filter

theorem _root_.GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family : ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | exact GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | (intros; apply GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family <;> assumption)
