module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalBranchesOfSeparableReduction
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_formal_branches_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  first | exact @GlobalTheory.branches_of_unramified_point | exact GlobalTheory.branches_of_unramified_point | (intros; apply GlobalTheory.branches_of_unramified_point <;> assumption)
