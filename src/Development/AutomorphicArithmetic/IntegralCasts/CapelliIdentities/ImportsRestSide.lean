module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

theorem UpperTheory.Reformulated.B.Yhc6.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) (m : ℕ),
      ((↑g : Matrix (Fin n) (Fin n) k) * x * (↑g⁻¹ : Matrix (Fin n) (Fin n) k)) ^ m =
        (↑g : Matrix (Fin n) (Fin n) k) * x ^ m * (↑g⁻¹ : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ _ _ n g x m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
