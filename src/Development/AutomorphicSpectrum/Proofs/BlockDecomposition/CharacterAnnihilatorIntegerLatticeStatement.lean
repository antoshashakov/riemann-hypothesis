module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAnnihilatorIntegerLattice
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open ValuativeRel MeasureTheory Matrix

theorem _root_.GlobalTheory.T.character_annihilator_integer_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 → IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧ IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | exact GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | (intros; apply GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator <;> assumption)
