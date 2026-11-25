module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvEntryNormLeOfSubSmulOnePosSemidef
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ i j, ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by
  first | exact @GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | exact GlobalTheory.inv_entry_norm_le_of_sub_posSemidef | (intros; apply GlobalTheory.inv_entry_norm_le_of_sub_posSemidef <;> assumption)
