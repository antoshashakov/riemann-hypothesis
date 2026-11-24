module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulStdBlock
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_det_one_mul_stdBlock' : ∀ {K : Type} [Field K] {n r : ℕ}, r < n → ∀ y : Matrix (Fin n) (Fin r) K, y.rank = r → ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧ g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  first | exact @GlobalTheory.exists_det_one_mul_stdBlock | exact GlobalTheory.exists_det_one_mul_stdBlock | (intros; apply GlobalTheory.exists_det_one_mul_stdBlock <;> assumption)
