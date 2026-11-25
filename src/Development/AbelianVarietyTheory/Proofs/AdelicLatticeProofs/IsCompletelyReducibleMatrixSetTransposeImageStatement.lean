module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleMatrixSetTransposeImage
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_transpose | exact GlobalTheory.ClassFin.ss_transpose | (intros; apply GlobalTheory.ClassFin.ss_transpose <;> assumption)
