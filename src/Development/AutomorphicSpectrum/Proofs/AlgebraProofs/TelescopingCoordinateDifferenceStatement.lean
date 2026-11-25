module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TelescopingCoordinateDifference
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.telescoping_coordinate_difference : ∀ (α : Type) (n : ℕ) (F : (Fin n → α) → ℝ) (a b : Fin n → α), F a - F b = ∑ i : Fin n, (F (fun j => if j < i then b j else a j) - F (fun j => if j ≤ i then b j else a j)) := by
  first | exact @GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions | exact GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions | (intros; apply GlobalTheory.CompanionTheory.Telescope.telescope_fin_positions <;> assumption)
