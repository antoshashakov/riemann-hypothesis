module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinNormTensorStabilizerConjTransposeInvariant
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.minNormTensor_stabilizer_conjTranspose_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsMinVec d v → ∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v := by
  first | exact @GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec | exact GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec | (intros; apply GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec <;> assumption)
