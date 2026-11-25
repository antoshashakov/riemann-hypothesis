module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EntriesBoundedOfConjSpanningBounded
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  first | exact @GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | exact GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | (intros; apply GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded <;> assumption)
