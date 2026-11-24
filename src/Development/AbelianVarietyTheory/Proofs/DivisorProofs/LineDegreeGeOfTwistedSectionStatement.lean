module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeGeOfTwistedSection
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem _root_.GlobalTheory.T.lineDegree_ge_of_twisted_section : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ (n : ℕ) (h : Place k F → Matrix (Fin n) (Fin n) F), admitted h → ∀ (v₀ : Place k F) (π : F), π ≠ 0 → ord v₀ π = 1 → ∀ (e : ℤ) (p : Fin n → F), p ≠ 0 → (∀ (v : Place k F) (i : Fin n), v.1 ((twistAt v₀ (π ^ (-e)) h v).mulVec p i) ≤ 1) → e ≤ degLine h p := by
  first | exact @GlobalTheory.Nef.degLine_ge_of_twist | exact GlobalTheory.Nef.degLine_ge_of_twist | (intros; apply GlobalTheory.Nef.degLine_ge_of_twist <;> assumption)
