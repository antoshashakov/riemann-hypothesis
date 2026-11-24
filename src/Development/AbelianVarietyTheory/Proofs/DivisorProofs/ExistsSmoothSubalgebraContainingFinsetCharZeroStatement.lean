module

public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSubalgebraContainingFinsetCharZero
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by
  first | exact @GlobalTheory.exists_smooth_subalgebra_of_finset | exact GlobalTheory.exists_smooth_subalgebra_of_finset | (intros; apply GlobalTheory.exists_smooth_subalgebra_of_finset <;> assumption)
