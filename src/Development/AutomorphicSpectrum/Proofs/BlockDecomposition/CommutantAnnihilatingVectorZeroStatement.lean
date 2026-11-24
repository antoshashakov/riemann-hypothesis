module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZero
import Supplements.MathlibImports.AnalysisAndTactics
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.commutant_annihilating_vector_zero : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (v : Fin m → ℂ), IsUnit g.det → Function.Injective d → (∀ i, (g⁻¹ *ᵥ v) i ≠ 0) → ∀ A : Matrix (Fin m) (Fin m) ℂ, A * (g * diagonal d * g⁻¹) = (g * diagonal d * g⁻¹) * A → A *ᵥ v = 0 → A = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | exact GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero <;> assumption)
