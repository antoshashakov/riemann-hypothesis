module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LatticeSumDilateHaarAsymptotic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.lattice_sum_dilate_haar_asymptotic : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  exact @GlobalTheory.lattice_sum_dilate_haar
