module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCountFromHyperplanes
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf

@[expose] public section

open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

theorem _root_.GlobalTheory.T.hermitian_count_from_hyperplanes : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (w : (Fin (n + 1) → k) → V) (c A : ℝ),
  (∀ x, 0 ≤ (B x x).re) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 →
    Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a b : Fin (n + 1) → k, a ≠ 0 → (∀ s : k, b ≠ s • a) →
    Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → w (s • a) = w a) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → (B (w a) (w a)).re = c) →
  (∀ x : Fin (n + 1) → k, x ≠ 0 →
    (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)
       (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)).re = A) →
  (Fintype.card k : ℝ) ^ n * c ≤ (Fintype.card k : ℝ) * A := by
  first | exact @GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts | exact GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts | (intros; apply GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts <;> assumption)
