module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSymplecticFixesSiegelPointI
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → sᵀ * s = 1 → P.det ≠ 0 → GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | exact GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | (intros; apply GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic <;> assumption)
