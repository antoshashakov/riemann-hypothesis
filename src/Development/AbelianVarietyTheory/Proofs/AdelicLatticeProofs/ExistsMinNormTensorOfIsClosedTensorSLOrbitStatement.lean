module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsMinNormTensorOfIsClosedTensorSLOrbit
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_minNormTensor_of_isClosed_tensorSLOrbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∃ w ∈ orb d v, IsMinVec d w := by
  first | exact @GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | exact GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | (intros; apply GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed <;> assumption)
